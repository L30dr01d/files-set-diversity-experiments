from __future__ import annotations

import sys
from collections.abc import Callable, Iterator, Mapping, Sequence
from heapq import merge
from math import ceil, floor
from pathlib import Path

from experiment_runner.config import Experiment
from experiment_runner.instrumented_analyzers import (
    ANALYZERS,
    DESIGN_TIMEOUT_SECONDS,
    RunFile,
    RunSet,
    default_run_file,
    default_run_set,
    ensure_analyzers,
)
from experiment_runner.paths import dataset_dir
from experiment_runner.timeout import call_timed
from fast_filter.suite import list_test_files, write_suite_file

BUDGET_PERCENTS = (100, 75, 50, 25)
FILTER_DRAWS = 10
ReduceFn = Callable[[Path, str, float], list[str]]
AdequateFn = Callable[[Path, Path], list[int]]
PLOT_ROWS = (*reversed(ANALYZERS), ("both", "Both tools", "C2"))
COLUMNS = (
    ("line", "Line coverage", False),
    ("line", "Line adequacy", True),
    ("mcdc", "MC/DC coverage", False),
    ("mcdc", "MC/DC adequacy", True),
    ("joint", "Line and MC/DC adequacy", True),
)


def plot_coverage_bars(results: dict, experiment: Experiment, dataset_size: int):
    import matplotlib.pyplot as plt
    from matplotlib.ticker import MaxNLocator

    fig, axes = plt.subplots(
        len(PLOT_ROWS), len(COLUMNS), figsize=(18, 10), constrained_layout=True
    )
    fig.suptitle(f"{experiment.title} ({experiment.datasets[0]})")
    files_kept_panels = []
    scale_groups = [files_kept_panels]
    for row, (tool, label, color) in enumerate(PLOT_ROWS):
        for col, (metric, title, adequate) in enumerate(COLUMNS):
            ax = axes[row, col]
            if tool == "both" and not adequate:
                ax.set_visible(False)
                continue
            if adequate:
                samples = [[
                    100 * count / dataset_size if dataset_size else 0.0
                    for count in results["adequacy"][tool][metric]
                ]]
                files_kept_panels.append((ax, samples))
                ax.set_xticks([])
                ylabel = "Files kept (%)"
                ax.set_ylabel(f"{label}\n{ylabel}" if tool == "both" and col == 1 else ylabel)
            else:
                samples = [
                    [draw[metric] for draw in results["budgets"][tool][str(percent)]]
                    for percent in BUDGET_PERCENTS
                ]
                scale_groups.append([(ax, samples)])
                ax.set_xticks(range(1, len(BUDGET_PERCENTS) + 1), [f"{p}%" for p in BUDGET_PERCENTS])
                ax.set_ylabel(f"{label}\nCoverage (%)" if col == 0 else "Coverage (%)")
            ax.boxplot(
                samples,
                widths=0.6,
                patch_artist=True,
                manage_ticks=False,
                boxprops={"facecolor": color},
                medianprops={"color": "black"},
            )
            if row == 0:
                ax.set_title(title)
            ax.grid(axis="y", alpha=0.3)
    for panels in scale_groups:
        values = [value for _, samples in panels for draws in samples for value in draws]
        low, high = min(values), max(values)
        padding = max(0.5, 0.05 * (high - low))
        limits = floor(low - padding), ceil(high + padding)
        for ax, _ in panels:
            ax.set_ylim(*limits)
            ax.yaxis.set_major_locator(MaxNLocator(integer=True))
    return fig


def _default_reduce(files_dir: Path, algo: str, percent: float) -> list[str]:
    from fast_filter import reduce

    return reduce(files_dir, algo, percent)


def _default_adequate(suite_path: Path, whitebox_path: Path) -> list[int]:
    import fastr_adequate

    selected = fastr_adequate.fastPlusPlus(str(suite_path), str(whitebox_path))[3]
    return [int(tc_id) for tc_id in selected]


def _stored_profiles(
    analyzer: str,
    paths: Sequence[Path],
    run_file: RunFile,
    profile_root: Path,
    timeout: float,
) -> list[Path | None]:
    hits = []
    for source in paths:
        directory = profile_root / analyzer / source.name
        directory.mkdir(parents=True, exist_ok=True)
        print(f"coverage: {analyzer} {source.name}", file=sys.stderr, flush=True)
        hits.append(call_timed(
            run_file, (analyzer, source, directory), timeout=timeout,
            memory_bytes=None, raise_errors=True,
        ))
    return hits


def _tokens(path: Path | None, goal: str, prefix: str) -> Iterator[str]:
    if path is None:
        return
    with path.open(encoding="utf-8") as stream:
        for row in stream:
            token = row.rstrip("\n")
            if goal == "joint" or token.startswith("L" if goal == "line" else "M"):
                yield token[:1] + prefix + token[1:]


def _adequate_counts(
    paths: Sequence[Path],
    stored: Mapping[str, Sequence[Path | None]],
    adequate_fn: AdequateFn,
    work: Path,
) -> dict[str, dict[str, list[int]]]:
    counts = {}
    for tool in [*stored, "both"]:
        sources = stored if tool == "both" else {tool: stored[tool]}
        counts[tool] = {}
        for goal in ("line", "mcdc", "joint"):
            directory = work / tool / goal
            directory.mkdir(parents=True, exist_ok=True)
            suite = directory / "suite.txt"
            whitebox = directory / "whitebox.txt"
            write_suite_file(list(paths), suite)
            has_hits = False
            with whitebox.open("w", encoding="utf-8") as output:
                for per_file in zip(*sources.values(), strict=True):
                    groups = (
                        _tokens(path, goal, f"{name}:" if tool == "both" else "")
                        for name, path in zip(sources, per_file, strict=True)
                    )
                    separator = ""
                    for token in merge(*groups):
                        output.write(separator + token)
                        separator = " "
                        has_hits = True
                    output.write("\n")
            draws = []
            for _ in range(FILTER_DRAWS):
                selected = adequate_fn(suite, whitebox) if has_hits else []
                for tc_id in selected:
                    if not 1 <= int(tc_id) <= len(paths):
                        raise ValueError(f"selection id {tc_id} out of range")
                draws.append(len(selected))
            counts[tool][goal] = draws
    return counts


def _write_figure(
    results: dict, experiment: Experiment, output_dir: Path, dataset_size: int
) -> None:
    import matplotlib

    matplotlib.use("Agg")
    import matplotlib.pyplot as plt

    fig = plot_coverage_bars(results, experiment, dataset_size)
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
    render: bool = True,
    run_file: RunFile = default_run_file,
    run_set: RunSet = default_run_set,
    reduce_fn: ReduceFn | None = None,
    adequate_fn: AdequateFn | None = None,
    timeout: float = DESIGN_TIMEOUT_SECONDS,
) -> dict:
    if len(experiment.datasets) != 1:
        raise ValueError("coverage_with_filter requires exactly one dataset")
    if reduce_fn is None:
        reduce_fn = _default_reduce
    if adequate_fn is None:
        adequate_fn = _default_adequate
    if run_file is default_run_file or run_set is default_run_set:
        ensure_analyzers()

    dataset_name = experiment.datasets[0]
    files_dir = dataset_dir(root, dataset_name)
    paths = list_test_files(files_dir)
    paths_by_name = {path.name: path for path in paths}
    profile_root = output_dir / "profiles" / dataset_name
    budgets: dict[str, dict[str, list[dict[str, float]]]] = {
        tool: {} for tool, _, _ in ANALYZERS
    }
    for percent in BUDGET_PERCENTS:
        category = str(percent)
        for samples in budgets.values():
            samples[category] = []
        for draw in range(FILTER_DRAWS):
            selected = paths
            if percent != 100:
                names = reduce_fn(files_dir, "FAST++", percent)
                try:
                    selected = [paths_by_name[name] for name in names]
                except KeyError as exc:
                    raise ValueError(f"unknown kept basename: {exc.args[0]}") from exc
            for tool, samples in budgets.items():
                draw_dir = profile_root / "budgets" / str(percent) / str(draw) / tool
                samples[category].append(run_set(tool, selected, draw_dir, timeout))

    stored = {
        tool: _stored_profiles(tool, paths, run_file, profile_root, timeout)
        for tool in budgets
    }
    counts = _adequate_counts(
        paths, stored, adequate_fn, output_dir / "adequate" / dataset_name
    )
    results = {"budgets": budgets, "adequacy": counts}
    if not render:
        return {**results, "dataset_size": len(paths)}
    _write_figure(results, experiment, output_dir, len(paths))
    return results
