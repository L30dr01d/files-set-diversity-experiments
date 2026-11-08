from __future__ import annotations

import json
import os
import shutil
import subprocess
import sys
import tempfile
import time
from collections.abc import Callable, Mapping, Sequence
from pathlib import Path

from experiment_runner.analyzer_coverage import (
    ImageCoverage,
    adequate_tick,
    combine_images,
    hits_from_llvm_export,
    iverilog_command,
    profile_env,
    subset_percents,
    verilator_command,
    whitebox_line,
)
from experiment_runner.config import Experiment
from experiment_runner.paths import dataset_dir
from experiment_runner.timeout import call_timed
from fast_filter.suite import list_test_files, write_suite_file

DESIGN_TIMEOUT_SECONDS = 120
CATEGORIES = ("100", "75", "50", "25", "adequate")
BUDGET_PERCENTS = (75, 50, 25)
RunFile = Callable[
    [str, Path, Path], ImageCoverage | dict[str, ImageCoverage | None] | None
]
ReduceFn = Callable[[Path, str, float], list[str]]
AdequateFn = Callable[[Path, Path], list[int]]
ANALYZERS = (
    ("iverilog", "Icarus", "C0"),
    ("verilator", "Verilator", "C1"),
)
COLUMNS = (("line", "Line coverage"), ("mcdc", "MC/DC"))


def plot_coverage_bars(results: dict, experiment: Experiment):
    import matplotlib.pyplot as plt

    datasets = list(experiment.datasets)
    fig, axes = plt.subplots(
        len(datasets),
        2,
        figsize=(12, 5 * len(datasets)),
        squeeze=False,
        constrained_layout=True,
    )
    fig.suptitle(experiment.title)
    positions = list(range(len(CATEGORIES)))
    width = 0.4
    for row, dataset in enumerate(datasets):
        icarus = results[dataset]["iverilog"]["adequate"]
        verilator = results[dataset]["verilator"]["adequate"]
        if (icarus["kept"], icarus["total"]) == (verilator["kept"], verilator["total"]):
            adequate_label = adequate_tick(icarus["kept"], icarus["total"])
        else:
            adequate_label = (
                "adequate\n"
                f"Icarus {icarus['kept']} files, {round(100 * icarus['kept'] / icarus['total'])}%\n"
                f"Verilator {verilator['kept']} files, {round(100 * verilator['kept'] / verilator['total'])}%"
            )
        tick_labels = [f"{category}%" for category in CATEGORIES[:-1]]
        tick_labels.append(adequate_label)
        for col, (field, title) in enumerate(COLUMNS):
            ax = axes[row][col]
            peak = 0.0
            for shift, (analyzer, series, color) in zip((-width / 2, width / 2), ANALYZERS):
                heights = [
                    float(results[dataset][analyzer][category][field])
                    for category in CATEGORIES
                ]
                peak = max(peak, *heights)
                bars = ax.bar(
                    [position + shift for position in positions],
                    heights,
                    width=width,
                    color=color,
                    label=series,
                )
                ax.bar_label(bars, fmt="%.1f", padding=2, fontsize=9)
            ax.set_title(title)
            ax.set_ylabel("%")
            ax.set_xticks(positions, tick_labels)
            ax.set_xlim(-0.5, len(CATEGORIES) - 0.5)
            ax.set_ylim(0, max(peak * 1.25, 1))
            ax.legend(fontsize=8)
            ax.grid(axis="y", alpha=0.3)
    return fig


def _default_reduce(files_dir: Path, algo: str, percent: float) -> list[str]:
    from fast_filter import reduce

    return reduce(files_dir, algo, percent)


def _default_adequate(suite_path: Path, whitebox_path: Path) -> list[int]:
    import fastr_adequate

    selected = fastr_adequate.fastPlusPlus(str(suite_path), str(whitebox_path))[3]
    return [int(tc_id) for tc_id in selected]


def _empty_coverage(donor: ImageCoverage | None) -> ImageCoverage:
    if donor is None:
        return ImageCoverage(
            line_hits=frozenset(),
            line_universe=frozenset(),
            mcdc_hits=frozenset(),
            mcdc_universe=frozenset(),
        )
    return ImageCoverage(
        line_hits=frozenset(),
        line_universe=donor.line_universe,
        mcdc_hits=frozenset(),
        mcdc_universe=donor.mcdc_universe,
    )


def _coverages_from_runs(recorded: Sequence[object]) -> list[ImageCoverage]:
    # call_timed starts a fresh process, so image universes travel back in the
    # return value. A dict is one image's export; ImageCoverage is an injected run.
    if not any(isinstance(item, dict) for item in recorded):
        donor = next((item for item in recorded if isinstance(item, ImageCoverage)), None)
        return [
            item if isinstance(item, ImageCoverage) else _empty_coverage(donor) for item in recorded
        ]
    remembered: dict[str, ImageCoverage] = {}
    combined: list[ImageCoverage | None] = []
    stems: list[str] = []
    for item in recorded:
        if not isinstance(item, dict):
            combined.append(None)
            continue
        parts: list[ImageCoverage] = []
        for stem, coverage in item.items():
            if stem not in stems:
                stems.append(stem)
            if isinstance(coverage, ImageCoverage):
                previous = remembered.get(stem)
                remembered[stem] = coverage if previous is None else combine_images([previous, coverage])
                parts.append(coverage)
            elif stem in remembered:
                parts.append(_empty_coverage(remembered[stem]))
            else:
                parts.append(_NO_HITS)
        combined.append(combine_images(parts) if parts else _NO_HITS)
    missing = [stem for stem in stems if stem not in remembered]
    if missing:
        raise RuntimeError(f"profile export failed for {', '.join(missing)}")
    donor = next((item for item in combined if item is not None), None)
    return [item if item is not None else _empty_coverage(donor) for item in combined]


def _stored_profiles(
    analyzer: str,
    paths: Sequence[Path],
    run_file: RunFile,
    profile_root: Path,
    timeout: float,
) -> list[ImageCoverage]:
    recorded: list[object] = []
    for source in paths:
        profile_dir = profile_root / analyzer / source.name
        profile_dir.mkdir(parents=True, exist_ok=True)
        print(f"coverage: {analyzer} {source.name}", file=sys.stderr, flush=True)
        started = time.monotonic()
        # llvm-cov export of verilator_bin exceeds the 4 GiB score cap and
        # returns "LLVM ERROR: out of memory", which drops that image.
        value = call_timed(
            run_file,
            (analyzer, source, profile_dir),
            timeout=timeout,
            memory_bytes=None,
        )
        if value is None and time.monotonic() - started >= timeout:
            print(
                f"warning: {analyzer} {source.name} timed out after {timeout:g}s",
                file=sys.stderr,
                flush=True,
            )
        recorded.append(value)
    return _coverages_from_runs(recorded)


def _scores(
    files: Sequence[ImageCoverage],
    universe: ImageCoverage,
    kept: int,
    total: int,
) -> dict:
    line, mcdc = subset_percents(files, universe)
    return {"line": line, "mcdc": mcdc, "kept": kept, "total": total}


def _coverages_named(
    names: Sequence[str], by_name: dict[str, ImageCoverage]
) -> list[ImageCoverage]:
    missing = [name for name in names if name not in by_name]
    if missing:
        raise ValueError(f"unknown kept basename: {missing[0]}")
    return [by_name[name] for name in names]


def _select_adequate(
    paths: Sequence[Path],
    coverages: Sequence[ImageCoverage],
    adequate_fn: AdequateFn,
    work: Path,
) -> list[str]:
    work.mkdir(parents=True, exist_ok=True)
    suite_path = work / "suite.txt"
    whitebox_path = work / "whitebox.txt"
    write_suite_file(list(paths), suite_path)
    whitebox_path.write_text(
        "".join(f"{whitebox_line(coverage)}\n" for coverage in coverages),
        encoding="utf-8",
    )
    names = [path.name for path in paths]
    selected: list[str] = []
    for tc_id in adequate_fn(suite_path, whitebox_path):
        index = int(tc_id) - 1
        if index < 0 or index >= len(names):
            raise ValueError(f"selection id {tc_id} out of range")
        selected.append(names[index])
    return selected


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
_NO_HITS = ImageCoverage(
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


def _run_analyzer(command: list[str], profile_dir: Path) -> None:
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
        subprocess.run(command, env=env, check=False, capture_output=True)
    except OSError as exc:
        raise RuntimeError(f"analyzer failed to start: {exc}") from exc


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
    profraws = sorted(profile_dir.glob("*.profraw"))
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


def default_run_file(
    analyzer: str, source: Path, profile_dir: Path
) -> dict[str, ImageCoverage | None] | None:
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
    with tempfile.TemporaryDirectory() as scratch_name:
        scratch = Path(scratch_name)
        if analyzer == "iverilog":
            command = iverilog_command(iverilog, source, scratch / "a.out")
        else:
            command = verilator_command(verilator, source, scratch / "mdir")
        _run_analyzer(command, profile_dir)
    return _coverage_from_profiles(profile_dir, stems, images, signatures)


def _write_figure(results: dict, experiment: Experiment, output_dir: Path) -> None:
    import matplotlib

    matplotlib.use("Agg")
    import matplotlib.pyplot as plt

    fig = plot_coverage_bars(results, experiment)
    output_dir.mkdir(parents=True, exist_ok=True)
    png = output_dir / f"{experiment.id}.png"
    try:
        fig.savefig(png, dpi=180)
        fig.savefig(png.with_suffix(".svg"))
    finally:
        plt.close(fig)
    if not png.is_file():
        raise RuntimeError(f"PNG not written: {png}")
    if not png.with_suffix(".svg").is_file():
        raise RuntimeError(f"SVG not written: {png.with_suffix('.svg')}")


def run_coverage_with_filter(
    experiment: Experiment,
    root: Path,
    *,
    output_dir: Path,
    run_file: RunFile = default_run_file,
    reduce_fn: ReduceFn | None = None,
    adequate_fn: AdequateFn | None = None,
    timeout: float = DESIGN_TIMEOUT_SECONDS,
) -> dict:
    if reduce_fn is None:
        reduce_fn = _default_reduce
    if adequate_fn is None:
        adequate_fn = _default_adequate
    # call_timed turns a failed run_file into an empty cell and the figure
    # is still written. A missing llvm tool or a failed build must abort first.
    if run_file is default_run_file:
        ensure_analyzers()
    results: dict = {}
    for dataset_name in experiment.datasets:
        files_dir = dataset_dir(root, dataset_name)
        paths = list_test_files(files_dir)
        total = len(paths)
        stored = {
            analyzer: _stored_profiles(
                analyzer,
                paths,
                run_file,
                output_dir / "profiles" / dataset_name,
                timeout,
            )
            for analyzer, _series, _color in ANALYZERS
        }
        budgets = {
            str(percent): list(reduce_fn(files_dir, "FAST++", percent))
            for percent in BUDGET_PERCENTS
        }
        dataset_results: dict = {}
        for analyzer, _series, _color in ANALYZERS:
            coverages = stored[analyzer]
            universe = combine_images(coverages)
            by_name = {path.name: coverage for path, coverage in zip(paths, coverages)}
            kept_names = _select_adequate(
                paths,
                coverages,
                adequate_fn,
                output_dir / "adequate" / dataset_name / analyzer,
            )
            cells = {"100": _scores(coverages, universe, total, total)}
            for percent in BUDGET_PERCENTS:
                names = budgets[str(percent)]
                cells[str(percent)] = _scores(
                    _coverages_named(names, by_name),
                    universe,
                    len(names),
                    total,
                )
            cells["adequate"] = _scores(
                _coverages_named(kept_names, by_name),
                universe,
                len(kept_names),
                total,
            )
            dataset_results[analyzer] = cells
        results[dataset_name] = dataset_results
    _write_figure(results, experiment, output_dir)
    return results
