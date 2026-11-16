from __future__ import annotations

import tempfile
import time
from collections.abc import Callable, Mapping
from pathlib import Path

from experiment_runner.config import Experiment
from experiment_runner.paths import dataset_dir, load_score
from experiment_runner.plotting import tool_color
from experiment_runner.score_for_fastr import list_basenames, stage_kept
from experiment_runner.score_per_measure import ScoreFn, measure_dataset
from experiment_runner.timeout import SCORE_TIMEOUT_SECONDS, call_timed
from panhard_filter import FilterResult, filter_paths

PANHARD = "panhard-measure"
FilterFn = Callable[..., FilterResult]


def _run_filter(
    filter_fn: FilterFn, path_strs: tuple[str, ...], ranking: str
) -> FilterResult:
    return filter_fn([Path(p) for p in path_strs], dont_stop=True, ranking=ranking)


def run_score_for_panhard(
    experiment: Experiment,
    root: Path,
    *,
    ranking: str,
    score_fns: Mapping[str, ScoreFn] | None = None,
    filter_fn: FilterFn | None = None,
    monotonic=None,
    timeout: float = SCORE_TIMEOUT_SECONDS,
    output_dir: Path,
) -> dict:
    tools = tuple(experiment.tools)
    if score_fns is None:
        score_fns = {name: load_score(name) for name in tools if name != PANHARD}
    if filter_fn is None:
        filter_fn = filter_paths
    clock = monotonic or time.monotonic
    results: dict = {}
    for dataset_name in experiment.datasets:
        files_dir = dataset_dir(root, dataset_name)
        names = list_basenames(files_dir)
        paths = [files_dir / name for name in names]
        print(f"{dataset_name} {PANHARD} dont-stop", flush=True)
        t0 = clock()
        raw = call_timed(
            _run_filter,
            (filter_fn, tuple(str(p) for p in paths), ranking),
            timeout=timeout,
        )
        filter_seconds = float(clock() - t0)
        if raw is None:
            results[dataset_name] = {
                "filter_seconds": filter_seconds,
                "stop_count": None,
                "steps": None,
            }
            print(f"{dataset_name} kept=null", flush=True)
            continue
        if not isinstance(raw, FilterResult):
            raise TypeError("filter_fn must return a FilterResult")
        steps: list[dict] = []
        for index, step in enumerate(raw.steps):
            measures = {
                PANHARD: {
                    "value": float(step.score),
                    "residual": float(step.residual),
                    "seconds": None,
                },
            }
            extras = tuple(tool for tool in tools if tool != PANHARD)
            if extras:
                output_dir.mkdir(parents=True, exist_ok=True)
                with tempfile.TemporaryDirectory(
                    prefix="panhard-filter-kept-", dir=output_dir
                ) as tmp:
                    dest = Path(tmp) / "kept"
                    stage_kept(files_dir, [path.name for path in step.remaining], dest)
                    for tool in extras:
                        measures[tool] = measure_dataset(
                            dest,
                            score_fn=score_fns[tool],
                            monotonic=monotonic,
                            timeout=timeout,
                        )
            steps.append(
                {
                    "index": index,
                    "remaining_count": int(step.remaining_count),
                    "measures": measures,
                }
            )
            values = " ".join(
                f"{tool}={measures[tool]['value']}" for tool in tools
            )
            print(
                f"{dataset_name} step={index} kept={step.remaining_count} {values}",
                flush=True,
            )
        results[dataset_name] = {
            "filter_seconds": filter_seconds,
            "stop_count": int(raw.stop_count),
            "steps": steps,
        }

    import matplotlib

    matplotlib.use("Agg")
    import matplotlib.pyplot as plt

    fig = plot_panhard_grid(results, experiment)
    output_dir.mkdir(parents=True, exist_ok=True)
    png = output_dir / f"{experiment.id}.png"
    try:
        fig.savefig(png, dpi=180)
        fig.savefig(png.with_suffix(".svg"))
    finally:
        plt.close(fig)
    if not png.is_file() or not png.with_suffix(".svg").is_file():
        raise RuntimeError(f"plot not written: {png}")
    return results


def plot_panhard_grid(results: dict, experiment: Experiment):
    import matplotlib.pyplot as plt

    datasets = list(experiment.datasets)
    tools = [PANHARD, *[tool for tool in experiment.tools if tool != PANHARD]]
    n = len(datasets)
    fig, axes = plt.subplots(
        n, 1, figsize=(10, 5 * n), squeeze=False, constrained_layout=True
    )
    fig.suptitle(experiment.title)
    for row, dataset in enumerate(datasets):
        ax = axes[row][0]
        ax.set_title(f"{dataset} — panhard-filter")
        ax.set_xlabel("files count")
        ax.set_ylabel("diversity")
        payload = results[dataset]
        steps = payload.get("steps") or []
        if not steps:
            continue
        positions = list(range(len(steps)))
        labels = [
            str(count) if count % 5 == 0 else ""
            for count in (int(step["remaining_count"]) for step in steps)
        ]
        for i, tool in enumerate(tools):
            ys = []
            for step in steps:
                value = step["measures"][tool]["value"]
                ys.append(float("nan") if value is None else float(value))
            color = tool_color(tool, i)
            if tool == PANHARD:
                residuals = [step["measures"][tool]["residual"] for step in steps]
                ax.fill_between(
                    positions,
                    [value - abs(residual) for value, residual in zip(ys, residuals)],
                    [value + abs(residual) for value, residual in zip(ys, residuals)],
                    color=color,
                    alpha=0.2,
                )
            ax.plot(
                positions,
                ys,
                marker="o",
                color=color,
                label=tool,
            )
        counts = [int(step["remaining_count"]) for step in steps]
        stop = payload.get("stop_count")
        if stop in counts:
            ax.axvline(counts.index(int(stop)), color="black", linestyle="--", label="panhard stop")
        ax.set_xticks(positions, labels)
        ax.legend(fontsize=8)
        ax.grid(axis="y", alpha=0.3)
    return fig
