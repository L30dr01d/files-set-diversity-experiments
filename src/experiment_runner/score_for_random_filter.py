from __future__ import annotations

import tempfile
import time
from collections.abc import Callable, Mapping, Sequence
from pathlib import Path
from random import Random

from experiment_runner.config import Experiment
from experiment_runner.paths import dataset_dir, load_score
from experiment_runner.plotting import tool_color
from experiment_runner.score_for_fastr import list_basenames, stage_kept
from experiment_runner.score_per_measure import ScoreFn, measure_dataset
from experiment_runner.timeout import SCORE_TIMEOUT_SECONDS, call_timed
from random_filter import SubsetResult

RELATIVE_EPS = 1e-5
MAX_TRIES = 10
RUN_COUNT = 10
SEEDS = (0, 1, 2, 3, 4, 5, 6, 7, 8, 9)

FilterFn = Callable[..., SubsetResult]


def _default_filter(paths, measure, *, relative_eps, max_tries, rng):
    from random_filter import filter_subset

    return filter_subset(
        paths,
        measure,
        relative_eps=relative_eps,
        max_tries=max_tries,
        rng=rng,
    )


def _timed_filter(
    filter_fn: FilterFn,
    path_strs: tuple[str, ...],
    measure: ScoreFn,
    relative_eps: float,
    max_tries: int,
    seed: int,
):
    paths = [Path(p) for p in path_strs]
    return filter_fn(
        paths,
        measure,
        relative_eps=relative_eps,
        max_tries=max_tries,
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


def _score_steps(
    raw: SubsetResult,
    *,
    files_dir: Path,
    filter_tool: str,
    extra_tools: tuple[str, ...],
    tools: tuple[str, ...],
    score_fns: Mapping[str, ScoreFn],
    monotonic,
    timeout: float,
    output_dir: Path,
    dataset_name: str,
    seed: int,
) -> list[dict]:
    serialized: list[dict] = []
    for step in raw.steps:
        measures = {
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
                    measures[tool] = measure_dataset(
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
                "measures": measures,
            }
        )
        values = " ".join(
            f"{tool}={_format_value(measures[tool]['value'])}" for tool in tools
        )
        print(
            f"{dataset_name} run={seed} step={step.index} kept={step.remaining_count} {values}",
            flush=True,
        )
    return serialized


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
        runs: list[dict] = []
        for seed in SEEDS:
            print(f"{dataset_name} run={seed} {filter_tool}", flush=True)
            t0 = clock()
            raw = call_timed(
                _timed_filter,
                (
                    filter_fn,
                    tuple(str(p) for p in paths),
                    score_fns[filter_tool],
                    RELATIVE_EPS,
                    MAX_TRIES,
                    seed,
                ),
                timeout=timeout,
            )
            filter_seconds = float(clock() - t0)
            if raw is None:
                runs.append(
                    {
                        "seed": seed,
                        "filter_seconds": filter_seconds,
                        "steps": None,
                    }
                )
                print(
                    f"{dataset_name} run={seed} kept=null "
                    + " ".join(f"{tool}=null" for tool in tools),
                    flush=True,
                )
                continue
            if not isinstance(raw, SubsetResult):
                raise TypeError("filter_fn must return a SubsetResult")
            serialized = _score_steps(
                raw,
                files_dir=files_dir,
                filter_tool=filter_tool,
                extra_tools=extra_tools,
                tools=tools,
                score_fns=score_fns,
                monotonic=monotonic,
                timeout=timeout,
                output_dir=output_dir,
                dataset_name=dataset_name,
                seed=seed,
            )
            runs.append(
                {
                    "seed": seed,
                    "filter_seconds": filter_seconds,
                    "steps": serialized,
                }
            )
        results[dataset_name] = {"runs": runs}

    import matplotlib

    matplotlib.use("Agg")
    import matplotlib.pyplot as plt

    fig = plot_steps_grid(results, experiment)
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
    return results


def plot_steps_grid(results: dict, experiment: Experiment):
    import matplotlib.pyplot as plt
    from matplotlib.patches import Patch

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
    n_tools = len(tools)
    width = 0.8 / max(n_tools, 1)
    for row, dataset in enumerate(datasets):
        ax = axes[row][0]
        ax.set_title(f"{dataset} — random-filter")
        ax.set_xlabel("remaining %")
        ax.set_ylabel("Score")
        ax.set_ylim(0.0, 1.0)
        runs = results[dataset].get("runs") or []
        landings: dict[int, list[dict]] = {}
        pct_by_count: dict[int, float] = {}
        for run in runs:
            steps = run.get("steps")
            if not steps:
                continue
            seen_counts: set[int] = set()
            for step in steps:
                count = int(step["remaining_count"])
                if count in seen_counts:
                    continue
                seen_counts.add(count)
                landings.setdefault(count, []).append(step)
                pct_by_count.setdefault(count, float(step["remaining_pct"]))
        counts = sorted(landings, reverse=True)
        if not counts:
            continue
        drew = False
        for i, tool in enumerate(tools):
            data: list[list[float]] = []
            positions: list[float] = []
            offset = (i - (n_tools - 1) / 2) * width
            for j, count in enumerate(counts):
                scores = []
                for step in landings[count]:
                    value = step["measures"][tool]["value"]
                    if value is not None:
                        scores.append(float(value))
                if scores:
                    data.append(scores)
                    positions.append(j + offset)
            if not data:
                continue
            bp = ax.boxplot(
                data,
                positions=positions,
                widths=width * 0.85,
                patch_artist=True,
                manage_ticks=False,
            )
            color = tool_color(tool, i)
            for box in bp["boxes"]:
                box.set_facecolor(color)
            drew = True
        ax.set_xticks(range(len(counts)))
        ax.set_xticklabels(
            [
                f"{pct_by_count[count]:.1f}%\n{count}\nn={len(landings[count])}"
                for count in counts
            ]
        )
        if drew:
            ax.legend(
                handles=[
                    Patch(facecolor=tool_color(tool, i), label=tool)
                    for i, tool in enumerate(tools)
                ],
                fontsize=8,
            )
        ax.grid(axis="y", alpha=0.3)
    return fig
