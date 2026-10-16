from __future__ import annotations

import tempfile
import time
from collections.abc import Callable, Mapping, Sequence
from pathlib import Path
from random import Random

from experiment_runner.config import Experiment
from experiment_runner.paths import dataset_dir, load_score
from experiment_runner.score_for_fastr import list_basenames, stage_kept
from experiment_runner.score_per_measure import ScoreFn, measure_dataset
from experiment_runner.timeout import SCORE_TIMEOUT_SECONDS, call_timed
from random_filter import SubsetResult

SEED = 0
RELATIVE_EPS = 1e-5
MAX_TRIES = 10
MIN_KEEP = 10

FilterFn = Callable[..., SubsetResult]


def _default_filter(paths, metric, *, relative_eps, max_tries, min_keep, rng):
    from random_filter import filter_subset

    return filter_subset(
        paths,
        metric,
        relative_eps=relative_eps,
        max_tries=max_tries,
        min_keep=min_keep,
        rng=rng,
    )


def _timed_filter(
    filter_fn: FilterFn,
    path_strs: tuple[str, ...],
    metric: ScoreFn,
    relative_eps: float,
    max_tries: int,
    min_keep: int,
    seed: int,
):
    paths = [Path(p) for p in path_strs]
    return filter_fn(
        paths,
        metric,
        relative_eps=relative_eps,
        max_tries=max_tries,
        min_keep=min_keep,
        rng=Random(seed),
    )


def _format_value(value: object) -> str:
    if value is None:
        return "null"
    return f"{float(value):.6f}"


def _remaining_names(remaining: Sequence[Path]) -> list[str]:
    names = [path.name for path in remaining]
    if len(names) != len(set(names)):
        duplicate = next(name for name in names if names.count(name) > 1)
        raise ValueError(f"repeated kept basename: {duplicate}")
    return names


def run_score_for_random_filter(
    experiment: Experiment,
    root: Path,
    *,
    score_fns: Mapping[str, ScoreFn] | None = None,
    filter_fn: FilterFn | None = None,
    monotonic=None,
    timeout: float = SCORE_TIMEOUT_SECONDS,
    output_dir: Path,
) -> dict:
    if score_fns is None:
        score_fns = {name: load_score(name) for name in experiment.tools}
    if filter_fn is None:
        filter_fn = _default_filter
    clock = monotonic or time.monotonic
    tools = tuple(experiment.tools)
    filter_tool = tools[0]
    extra_tools = tools[1:]
    results: dict = {}
    for dataset_name in experiment.datasets:
        files_dir = dataset_dir(root, dataset_name)
        names = list_basenames(files_dir)
        paths = [files_dir / name for name in names]
        print(f"{dataset_name} {filter_tool}", flush=True)
        t0 = clock()
        raw = call_timed(
            _timed_filter,
            (
                filter_fn,
                tuple(str(p) for p in paths),
                score_fns[filter_tool],
                RELATIVE_EPS,
                MAX_TRIES,
                MIN_KEEP,
                SEED,
            ),
            timeout=timeout,
        )
        filter_seconds = float(clock() - t0)
        if raw is None:
            results[dataset_name] = {
                "filter_seconds": filter_seconds,
                "steps": None,
            }
            print(
                f"{dataset_name} kept=null "
                + " ".join(f"{tool}=null" for tool in tools),
                flush=True,
            )
            continue
        if not isinstance(raw, SubsetResult):
            raise TypeError("filter_fn must return a SubsetResult")
        serialized: list[dict] = []
        for step in raw.steps:
            metrics = {
                filter_tool: {"value": float(step.score), "seconds": None},
            }
            if extra_tools:
                output_dir.mkdir(parents=True, exist_ok=True)
                with tempfile.TemporaryDirectory(
                    prefix="random-filter-kept-", dir=output_dir
                ) as tmp:
                    dest = Path(tmp) / "kept"
                    stage_kept(files_dir, _remaining_names(step.remaining), dest)
                    for tool in extra_tools:
                        metrics[tool] = measure_dataset(
                            dest,
                            score_fn=score_fns[tool],
                            monotonic=monotonic,
                            timeout=timeout,
                        )
            serialized.append(
                {
                    "index": int(step.index),
                    "remaining_count": int(step.remaining_count),
                    "remaining_pct": float(step.remaining_pct),
                    "metrics": metrics,
                }
            )
            values = " ".join(
                f"{tool}={_format_value(metrics[tool]['value'])}" for tool in tools
            )
            print(
                f"{dataset_name} step={step.index} kept={step.remaining_count} {values}",
                flush=True,
            )
        results[dataset_name] = {
            "filter_seconds": filter_seconds,
            "steps": serialized,
        }

    import matplotlib

    matplotlib.use("Agg")
    import matplotlib.pyplot as plt

    fig = plot_steps_grid(results, experiment)
    output_dir.mkdir(parents=True, exist_ok=True)
    png = output_dir / f"{experiment.id}.png"
    try:
        fig.savefig(png, dpi=180)
    finally:
        plt.close(fig)
    if not png.is_file():
        raise RuntimeError(f"PNG not written: {png}")
    return results


def plot_steps_grid(results: dict, experiment: Experiment):
    import matplotlib.pyplot as plt

    datasets = list(experiment.datasets)
    tools = list(experiment.tools)
    n = len(datasets)
    fig, axes = plt.subplots(
        n,
        1,
        figsize=(14, 5 * n),
        squeeze=False,
        constrained_layout=True,
    )
    fig.suptitle(experiment.title)
    filter_tool = tools[0]
    for row, dataset in enumerate(datasets):
        ax = axes[row][0]
        ax.set_title(f"{dataset} — random-filter")
        ax.set_xlabel("step")
        ax.set_ylabel("Score")
        ax.set_ylim(0.0, 1.0)
        steps = results[dataset]["steps"]
        if not steps:
            continue
        xs = [int(step["index"]) for step in steps]
        for i, tool in enumerate(tools):
            ys = []
            for step in steps:
                value = step["metrics"][tool]["value"]
                ys.append(float("nan") if value is None else float(value))
            ax.plot(xs, ys, marker="o", color=f"C{i}", label=tool)
        ax.set_xticks(xs)
        for step in steps:
            y = step["metrics"][filter_tool]["value"]
            if y is None:
                continue
            ax.annotate(
                f"{float(step['remaining_pct']):.1f}%\n{step['remaining_count']}",
                (int(step["index"]), float(y)),
                textcoords="offset points",
                xytext=(0, 8),
                ha="center",
            )
        ax.legend(fontsize=8)
        ax.grid(axis="y", alpha=0.3)
    return fig
