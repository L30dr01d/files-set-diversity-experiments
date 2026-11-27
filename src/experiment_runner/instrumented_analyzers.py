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
    iverilog_command,
    profile_env,
    verilator_command,
)

DESIGN_TIMEOUT_SECONDS = 120
ANALYZER_CLEANUP_SECONDS = 5
RunFile = Callable[[str, Path, Path], Path]
RunSet = Callable[[str, Sequence[Path], Path, float], dict[str, float]]
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


def _require_llvm() -> None:
    missing = [name for name in ("llvm-cov", "llvm-profdata", "jq") if shutil.which(name) is None]
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
            subprocess.run(
                command, env=env, check=False, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
            )
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


def _analyzer_images(analyzer: str) -> tuple[Path, dict[str, Path]]:
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
    return iverilog if analyzer == "iverilog" else verilator, images


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


# Keep FAST-R's historical basename, segment, and MC/DC condition IDs.
_HIT_FILTER = r'''
input | .data[0].files[] | .filename as $file | select($file | contains("obj_dir") | not)
| ($file | split("/") | last) as $name
| (.segments[] | select(.[3] and (.[5] | not) and .[2] > 0)
   | "L\($name):\(.[0])"),
  (.mcdc_records[] | . as $record
   | first(.[] | arrays | select(all(.[]; type == "boolean")))
   | to_entries[] | select(.value)
   | "M\($name):\($record[0]):\($record[1]):\(.key)")
'''


def default_run_file(analyzer: str, source: Path, profile_dir: Path) -> Path:
    executable, images = _analyzer_images(analyzer)
    hits = profile_dir / "hits.txt"
    with tempfile.TemporaryDirectory(dir=profile_dir) as directory:
        scratch = Path(directory)
        _profile_source(analyzer, source, scratch, executable)
        raws = sorted(scratch.glob("*.profraw"))
        if not raws:
            raise RuntimeError(f"{analyzer} produced no profile for {source}")
        command = _export_command(list(images.values()), raws, scratch)
        command.extend(["-skip-functions", "-skip-expansions"])
        if os.environ.get("GITHUB_ACTIONS") == "true":
            command = ["/usr/bin/time", "-v", *command]
        with tempfile.TemporaryFile(dir=scratch) as tokens:
            with subprocess.Popen(command, stdout=subprocess.PIPE) as export:
                assert export.stdout is not None
                try:
                    subprocess.run(["jq", "-nr", _HIT_FILTER], stdin=export.stdout,
                                   stdout=tokens, check=True)
                finally:
                    export.stdout.close()
                if export.wait():
                    raise subprocess.CalledProcessError(export.returncode, command)
            tokens.seek(0)
            with (scratch / "hits.txt").open("wb") as out:
                subprocess.run(["sort", "-u"], stdin=tokens, stdout=out,
                               env={**os.environ, "LC_ALL": "C"}, check=True)
        (scratch / "hits.txt").replace(hits)
    return hits


def _export_command(images: Sequence[Path], profraws: Sequence[Path], directory: Path) -> list[str]:
    command = ["llvm-cov", "export", str(images[0])]
    for image in images[1:]:
        command.extend(["-object", str(image)])
    profdata = directory / "merged.profdata"
    profile_list = directory / "profiles.txt"
    if profraws:
        # Large draws can exceed the operating system's command length limit.
        with profile_list.open("w", encoding="utf-8") as stream:
            for path in profraws:
                # An explicit weight preserves commas in the profile filename.
                stream.write(f"1,{path}\n")
        inputs = ["-f", str(profile_list)]
    else:
        # LLVM accepts empty text profiles, including versions without -empty-profile.
        profile_list.write_bytes(b"")
        inputs = [str(profile_list)]
    subprocess.run(["llvm-profdata", "merge", "-sparse", *inputs, "-o", str(profdata)], check=True)
    command.extend(["-instr-profile", str(profdata)])
    return [*command, "-ignore-filename-regex=^/usr/|obj_dir", "-num-threads=1"]


def _summary(images: Sequence[Path], profraws: Sequence[Path], directory: Path) -> dict[str, float]:
    command = [*_export_command(images, profraws, directory), "-summary-only"]
    fields = (
        ".data[0].totals | {line: .lines.percent, mcdc: .mcdc.percent} "
        '| select(all(.[]; type == "number" and . >= 0 and . <= 100))'
    )
    with subprocess.Popen(command, stdout=subprocess.PIPE) as export:
        assert export.stdout is not None
        try:
            result = subprocess.run(
                ["jq", "-ec", fields], stdin=export.stdout, stdout=subprocess.PIPE, check=True,
            )
        finally:
            export.stdout.close()
        if export.wait():
            raise subprocess.CalledProcessError(export.returncode, command)
    return json.loads(result.stdout)


def default_run_set(
    analyzer: str, sources: Sequence[Path], profile_dir: Path, timeout: float
) -> dict[str, float]:
    executable, images = _analyzer_images(analyzer)
    profile_dir.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(dir=profile_dir) as draw:
        profraws: list[Path] = []
        for index, source in enumerate(sources):
            raw_dir = Path(draw) / str(index)
            raw_dir.mkdir()
            print(f"coverage: {analyzer} {source.name}", file=sys.stderr, flush=True)
            completed = _profile_source(analyzer, source, raw_dir, executable, timeout=timeout)
            if completed:
                raws = sorted(raw_dir.glob("*.profraw"))
                if not raws:
                    raise RuntimeError(f"{analyzer} produced no profile for {source}")
                profraws.extend(raws)
            else:
                print(
                    f"warning: {analyzer} {source.name} timed out after {timeout:g}s",
                    file=sys.stderr, flush=True,
                )
        return _summary(list(images.values()), profraws, Path(draw))
