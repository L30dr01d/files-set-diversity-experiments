from __future__ import annotations

from pathlib import Path
from typing import TYPE_CHECKING

from experiment_runner.config import Experiment
from experiment_runner.instrumented_analyzers import (
    ANALYZERS,
    DESIGN_TIMEOUT_SECONDS,
    RunSet,
    default_run_set,
    ensure_analyzers,
)
from experiment_runner.paths import dataset_dir
from experiment_runner.score_for_fastr import list_basenames
from experiment_runner.score_for_panhard import FilterFn, timed_panhard_filter
from experiment_runner.timeout import SCORE_TIMEOUT_SECONDS
from panhard_filter import filter_paths

if TYPE_CHECKING:
    from matplotlib.figure import Figure


def run_coverage_with_filter_panhard(
    experiment: Experiment,
    root: Path,
    *,
    ranking: str,
    output_dir: Path,
    run_set: RunSet = default_run_set,
    filter_fn: FilterFn = filter_paths,
    timeout: float = DESIGN_TIMEOUT_SECONDS,
    filter_timeout: float = SCORE_TIMEOUT_SECONDS,
) -> dict:
    if run_set is default_run_set:
        ensure_analyzers()

    results = {}
    for dataset in experiment.datasets:
        directory = dataset_dir(root, dataset)
        paths = [directory / name for name in list_basenames(directory)]
        print(f"{dataset} panhard-filter {ranking} dont-stop", flush=True)
        trace = timed_panhard_filter(paths, ranking, filter_fn=filter_fn, timeout=filter_timeout)
        if trace is None:
            print(f"{dataset} panhard-filter returned no trace", flush=True)
            results[dataset] = {"stop_count": None, "steps": None}
            continue

        steps = []
        for index, step in enumerate(trace.steps):
            coverage = {}
            for tool, _, _ in ANALYZERS:
                profile_dir = output_dir / "profiles" / experiment.id / dataset / str(index) / tool
                coverage[tool] = run_set(tool, step.remaining, profile_dir, timeout)
            steps.append({
                "remaining_count": step.remaining_count,
                "score": step.score,
                "residual": step.residual,
                "coverage": coverage,
            })

        results[dataset] = {"stop_count": trace.stop_count, "steps": steps}

    import matplotlib

    matplotlib.use("Agg")
    import matplotlib.pyplot as plt

    output_dir.mkdir(parents=True, exist_ok=True)
    fig = plot_panhard_coverage(results, experiment)
    try:
        fig.savefig(output_dir / f"{experiment.id}.png", dpi=180)
        fig.savefig(output_dir / f"{experiment.id}.svg")
    finally:
        plt.close(fig)
    return results


def plot_panhard_coverage(results: dict, experiment: Experiment) -> Figure:
    import matplotlib.pyplot as plt
    from matplotlib.ticker import MaxNLocator

    datasets = experiment.datasets
    fig, axes = plt.subplots(
        3, len(datasets), sharex="col", squeeze=False,
        figsize=(6 * len(datasets), 9), constrained_layout=True,
    )
    fig.suptitle(experiment.title)
    for column, dataset in enumerate(datasets):
        diversity, line, mcdc = axes[:, column]
        diversity.set_title(dataset)
        diversity.set_ylabel("Diversity")
        line.set_ylabel("Line coverage (%)")
        mcdc.set_ylabel("MC/DC coverage (%)")
        mcdc.set_xlabel("Files remaining")
        payload = results[dataset]
        steps = payload["steps"]
        if steps is None:
            diversity.text(
                0.5, 0.5, "Panhard filter timeout or failure",
                ha="center", va="center", transform=diversity.transAxes,
            )
            continue

        counts = [step["remaining_count"] for step in steps]
        scores = [step["score"] for step in steps]
        residuals = [abs(step["residual"]) for step in steps]
        if len(counts) == 1:
            diversity.errorbar(
                counts, scores, yerr=residuals, fmt="o", capsize=4,
                label="Panhard diversity ± residual", zorder=3,
            )
        else:
            diversity.plot(counts, scores, label="Panhard diversity")
            diversity.fill_between(
                counts,
                [score - residual for score, residual in zip(scores, residuals)],
                [score + residual for score, residual in zip(scores, residuals)],
                alpha=0.2,
                label="Residual",
            )
        width = 0.4
        for axis, metric in ((line, "line"), (mcdc, "mcdc")):
            for index, (tool, label, color) in enumerate(ANALYZERS):
                axis.bar(
                    [count + (0.5 - index) * width for count in counts],
                    [step["coverage"][tool][metric] for step in steps],
                    width=width, label=label, color=color,
                )
        for axis in (diversity, line, mcdc):
            axis.axvline(
                payload["stop_count"], color="black", linestyle="--", label="Panhard stop"
            )
            axis.grid(axis="y", alpha=0.3)
        diversity.legend(fontsize=8)
        line.legend(fontsize=8)
        mcdc.set_xlim(max(counts) + 0.5, min(counts) - 0.5)
        mcdc.xaxis.set_major_locator(MaxNLocator(nbins=8, integer=True))
    return fig
