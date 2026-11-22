from __future__ import annotations

import json
import os
import shutil
import signal
import subprocess
import sys
import tempfile
from collections.abc import Callable, Sequence
from pathlib import Path

from experiment_runner.analyzer_coverage import (
    ImageCoverage,
    combine_images,
    hits_from_llvm_export,
    iverilog_command,
    profile_env,
    verilator_command,
)

DESIGN_TIMEOUT_SECONDS = 120
ANALYZER_CLEANUP_SECONDS = 5
RunFile = Callable[
    [str, Path, Path], ImageCoverage | dict[str, ImageCoverage | None] | None
]
RunSet = Callable[[str, Sequence[Path], Path, float], ImageCoverage | None]
ANALYZERS = (
    ("iverilog", "Icarus", "C0"),
    ("verilator", "Verilator", "C1"),
)


_COVERAGE_FLAGS = "-fprofile-instr-generate -fcoverage-mapping -fcoverage-mcdc"
_IMAGE_STEMS = {
    "iverilog": ("ivlpp", "ivl"),
    "verilator": ("verilator_bin",),
}
_IMAGE_RELATIVE = {
    "ivl": ("lib/ivl/ivl",),
    "ivlpp": ("lib/ivl/ivlpp",),
    "verilator_bin": ("bin/verilator_bin", "share/verilator/bin/verilator_bin"),
}
_KNOWN_STEMS = frozenset(_IMAGE_RELATIVE)
_SIGNATURES: dict[str, str | None] = {}
NO_HITS = ImageCoverage(
    line_hits=frozenset(),
    line_universe=frozenset(),
    mcdc_hits=frozenset(),
    mcdc_universe=frozenset(),
)


def _require_llvm() -> None:
    missing = [name for name in ("llvm-cov", "llvm-profdata") if shutil.which(name) is None]
    if missing:
        raise RuntimeError(f"{' and '.join(missing)} is absent")


def _compiler_env() -> dict[str, str]:
    env = os.environ.copy()
    env["CC"] = "clang"
    env["CXX"] = "clang++"
    # Icarus compiles vvp/draw_tt with $(BUILDCC) plus these CFLAGS.
    # AX_PROG_CC_FOR_BUILD selects gcc when CC_FOR_BUILD is unset.
    env["CC_FOR_BUILD"] = "clang"
    for name in ("CFLAGS", "CXXFLAGS", "LDFLAGS"):
        env[name] = f"{env.get(name, '')} {_COVERAGE_FLAGS}".strip()
    env.pop("VERILATOR_ROOT", None)
    env.pop("VERILATOR_BIN", None)
    return env


def _checked(command: list[str], *, cwd: Path, env: dict[str, str]) -> None:
    try:
        completed = subprocess.run(command, cwd=cwd, env=env, check=False)
    except OSError as exc:
        raise RuntimeError(f"analyzer build failed: {exc}") from exc
    if completed.returncode != 0:
        rendered = " ".join(command)
        raise RuntimeError(f"analyzer build failed: {rendered} exited {completed.returncode}")


def _clone(url: str, dest: Path, env: dict[str, str]) -> None:
    if (dest / ".git").is_dir():
        return
    if dest.exists():
        shutil.rmtree(dest)
    dest.parent.mkdir(parents=True, exist_ok=True)
    _checked(["git", "clone", "--depth", "1", url, str(dest)], cwd=dest.parent, env=env)


def _build_tree(src: Path, prefix: Path, env: dict[str, str], bootstrap: list[str]) -> None:
    jobs = str(os.cpu_count() or 1)
    _checked(bootstrap, cwd=src, env=env)
    _checked(["./configure", f"--prefix={prefix}"], cwd=src, env=env)
    _checked(["make", "-j", jobs], cwd=src, env=env)
    _checked(["make", "install"], cwd=src, env=env)


def _find_installed(prefix: Path, stem: str) -> Path | None:
    for relative in _IMAGE_RELATIVE[stem]:
        path = prefix / relative
        if path.is_file():
            return path
    matches = [
        path
        for path in prefix.rglob(stem)
        if path.is_file() and path.name == stem and os.access(path, os.X_OK)
    ]
    if len(matches) == 1:
        return matches[0]
    return None


def _install_ready(prefix: Path) -> bool:
    drivers = (prefix / "bin" / "iverilog", prefix / "bin" / "verilator")
    if not all(path.is_file() for path in drivers):
        return False
    return all(_find_installed(prefix, stem) is not None for stem in _KNOWN_STEMS)


def ensure_analyzers() -> tuple[Path, Path]:
    _require_llvm()
    prefix = (Path("output") / "analyzer-prefix").resolve()
    source = (Path("output") / "analyzer-src").resolve()
    iverilog = prefix / "bin" / "iverilog"
    verilator = prefix / "bin" / "verilator"
    if _install_ready(prefix):
        return iverilog, verilator
    env = _compiler_env()
    _clone("https://github.com/steveicarus/iverilog.git", source / "iverilog", env)
    _clone("https://github.com/verilator/verilator.git", source / "verilator", env)
    _build_tree(source / "iverilog", prefix, env, ["sh", "autoconf.sh"])
    _build_tree(source / "verilator", prefix, env, ["autoconf"])
    if not _install_ready(prefix):
        raise RuntimeError("analyzer build failed")
    return iverilog, verilator


def _clear_profraws(profile_dir: Path) -> None:
    for path in profile_dir.glob("*.profraw"):
        path.unlink()


def _run_analyzer(
    command: list[str], profile_dir: Path, *, timeout: float | None = None
) -> bool:
    # %m merges into <signature>_0.profraw, so a leftover file would only gain hits.
    _clear_profraws(profile_dir)
    env = os.environ.copy()
    env.update(profile_env(profile_dir))
    # A prefix install finds verilator_bin beside the wrapper. A foreign
    # VERILATOR_ROOT would profile some other binary.
    env.pop("VERILATOR_ROOT", None)
    env.pop("VERILATOR_BIN", None)
    try:
        # Probes and rejected sources are expected. Their text is not a run failure.
        if timeout is None:
            subprocess.run(command, env=env, check=False, capture_output=True)
            return True
        process = subprocess.Popen(
            command,
            env=env,
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
            start_new_session=True,
        )
    except OSError as exc:
        raise RuntimeError(f"analyzer failed to start: {exc}") from exc
    try:
        process.wait(timeout=timeout)
        return True
    except subprocess.TimeoutExpired:
        try:
            os.killpg(process.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
        try:
            process.wait(timeout=ANALYZER_CLEANUP_SECONDS)
        except subprocess.TimeoutExpired as exc:
            raise RuntimeError(
                f"could not reap analyzer PID {process.pid} after timing out: {command!r}"
            ) from exc
        return False


def _warn_profile(image: Path, detail: str) -> None:
    text = " ".join(detail.split()) or "profile export failed"
    print(f"warning: {image}: {text}", file=sys.stderr)


def _export_merged(image: Path, profraws: Sequence[Path]) -> ImageCoverage | None:
    profdata = profraws[0].with_name(f"{image.name}.profdata")
    print(f"coverage: llvm-profdata {image.name}", file=sys.stderr, flush=True)
    merge = subprocess.run(
        [
            "llvm-profdata",
            "merge",
            "-sparse",
            *[str(path) for path in profraws],
            "-o",
            str(profdata),
        ],
        check=False,
        capture_output=True,
        text=True,
    )
    if merge.returncode != 0:
        _warn_profile(image, merge.stderr)
        return None
    print(f"coverage: llvm-cov {image.name}", file=sys.stderr, flush=True)
    export_path = profdata.with_name(f"{image.name}.export.json")
    command = [
        "llvm-cov",
        "export",
        str(image),
        "-instr-profile",
        str(profdata),
        "-format=text",
        "-skip-functions",
        "-skip-expansions",
        "-ignore-filename-regex=^/usr/|obj_dir",
        "-num-threads=1",
    ]
    if os.environ.get("GITHUB_ACTIONS") == "true":
        command = ["/usr/bin/time", "-v", *command]
    with open(export_path, "wb") as export_file:
        export = subprocess.run(
            command,
            check=False,
            stdout=export_file,
            stderr=subprocess.PIPE,
        )
    export_bytes = os.path.getsize(export_path)
    print(
        f"coverage: llvm-cov {image.name} export {export_bytes} bytes",
        file=sys.stderr,
        flush=True,
    )
    raw_stderr = export.stderr
    if isinstance(raw_stderr, bytes):
        detail = raw_stderr.decode(errors="replace")
    else:
        detail = raw_stderr or ""
    if export.returncode != 0:
        _warn_profile(image, detail)
        export_path.unlink(missing_ok=True)
        return None
    if detail:
        print(detail, file=sys.stderr, end="" if detail.endswith("\n") else "\n", flush=True)
    try:
        with open(export_path, encoding="utf-8") as export_file:
            return hits_from_llvm_export(json.load(export_file))
    except (json.JSONDecodeError, OSError, KeyError, IndexError, TypeError):
        _warn_profile(image, detail)
        return None
    finally:
        export_path.unlink(missing_ok=True)


def assign_profraws(
    profraws: Sequence[Path], signatures: Mapping[str, str]
) -> dict[str, list[Path]]:
    assigned: dict[str, list[Path]] = {}
    for profraw in profraws:
        stem = profraw.stem
        if stem in _KNOWN_STEMS:
            image = stem
        elif stem in signatures:
            image = signatures[stem]
        else:
            continue
        assigned.setdefault(image, []).append(profraw)
    return assigned


def _calibrate_signature(image: Path) -> str | None:
    with tempfile.TemporaryDirectory() as directory:
        profile_dir = Path(directory)
        # ivl and ivlpp accept -V. --version is read as one short option per letter.
        for flag in ("-V", "--version"):
            _clear_profraws(profile_dir)
            _run_analyzer([str(image), flag], profile_dir)
            profraws = list(profile_dir.glob("*.profraw"))
            if len(profraws) == 1:
                return profraws[0].stem
    return None


def _image_signature(image: Path) -> str | None:
    key = str(image)
    if key not in _SIGNATURES:
        _SIGNATURES[key] = _calibrate_signature(image)
    return _SIGNATURES[key]


def _warn_unmatched(image: Path, names: Sequence[str]) -> None:
    if names:
        _warn_profile(image, "unmatched profraw " + " ".join(names))
    else:
        _warn_profile(image, "no profraw")


def _coverage_from_profiles(
    profile_dir: Path,
    stems: tuple[str, ...],
    images: dict[str, Path],
    signatures: Mapping[str, str],
) -> dict[str, ImageCoverage | None] | None:
    return _coverage_from_raws(sorted(profile_dir.glob("*.profraw")), stems, images, signatures)


def _coverage_from_raws(
    profraws: Sequence[Path],
    stems: tuple[str, ...],
    images: dict[str, Path],
    signatures: Mapping[str, str],
) -> dict[str, ImageCoverage | None] | None:
    if not profraws:
        return None
    assigned = assign_profraws(profraws, signatures)
    used = {path for group in assigned.values() for path in group}
    unmatched = [path.name for path in profraws if path not in used]
    missing = [stem for stem in stems if not assigned.get(stem)]
    for stem in missing:
        _warn_unmatched(images[stem], unmatched)
    if unmatched and not missing:
        _warn_unmatched(images[stems[0]], unmatched)
    exports: dict[str, ImageCoverage | None] = {}
    for stem in stems:
        files = assigned.get(stem, [])
        exports[stem] = _export_merged(images[stem], files) if files else None
    return exports


def _analyzer_images(analyzer: str) -> tuple[Path, dict[str, Path], dict[str, str]]:
    iverilog, verilator = ensure_analyzers()
    stems = _IMAGE_STEMS.get(analyzer)
    if stems is None:
        raise RuntimeError(f"unknown analyzer: {analyzer}")
    prefix = iverilog.parent.parent
    images: dict[str, Path] = {}
    for stem in stems:
        image = _find_installed(prefix, stem)
        if image is None:
            raise RuntimeError(f"analyzer build did not install {stem}")
        images[stem] = image
    signatures: dict[str, str] = {}
    for stem, image in images.items():
        signature = _image_signature(image)
        if signature is not None:
            signatures[signature] = stem
    return iverilog if analyzer == "iverilog" else verilator, images, signatures


def _profile_source(
    analyzer: str, source: Path, profile_dir: Path, executable: Path,
    *, timeout: float | None = None,
) -> bool:
    with tempfile.TemporaryDirectory() as scratch_name:
        scratch = Path(scratch_name)
        if analyzer == "iverilog":
            command = iverilog_command(executable, source, scratch / "a.out")
        else:
            command = verilator_command(executable, source, scratch / "mdir")
        return _run_analyzer(command, profile_dir, timeout=timeout)


def default_run_file(
    analyzer: str, source: Path, profile_dir: Path
) -> dict[str, ImageCoverage | None] | None:
    executable, images, signatures = _analyzer_images(analyzer)
    _profile_source(analyzer, source, profile_dir, executable)
    return _coverage_from_profiles(profile_dir, tuple(images), images, signatures)


def default_run_set(
    analyzer: str, sources: Sequence[Path], profile_dir: Path, timeout: float
) -> ImageCoverage:
    if not sources:
        return NO_HITS
    executable, images, signatures = _analyzer_images(analyzer)
    profile_dir.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(dir=profile_dir) as draw:
        profraws: list[Path] = []
        for index, source in enumerate(sources):
            raw_dir = Path(draw) / str(index)
            raw_dir.mkdir()
            print(f"coverage: {analyzer} {source.name}", file=sys.stderr, flush=True)
            completed = _profile_source(analyzer, source, raw_dir, executable, timeout=timeout)
            if completed:
                profraws.extend(sorted(raw_dir.glob("*.profraw")))
            else:
                print(
                    f"warning: {analyzer} {source.name} timed out after {timeout:g}s",
                    file=sys.stderr, flush=True,
                )
        exports = _coverage_from_raws(profraws, tuple(images), images, signatures) or {}
        return combine_images([coverage for coverage in exports.values() if coverage is not None])
