from __future__ import annotations

from collections.abc import Mapping
from pathlib import Path

from experiment_runner.config import Experiment
from experiment_runner.paths import dataset_dir, load_score
from experiment_runner.plotting import tool_color
from experiment_runner.score_per_measure import ScoreFn, _format_cell, measure_dataset
from experiment_runner.timeout import SCORE_TIMEOUT_SECONDS


def run_measure_per_set(
    experiment: Experiment,
    root: Path,
    *,
    score_fns: Mapping[str, ScoreFn] | None = None,
    monotonic=None,
    timeout: float = SCORE_TIMEOUT_SECONDS,
    output_dir: Path,
) -> dict:
    if score_fns is None:
        score_fns = {name: load_score(name) for name in experiment.tools}
    results: dict = {}
    for name in experiment.datasets:
        files_dir = dataset_dir(root, name)
        results[name] = {}
        for tool, score_fn in score_fns.items():
            print(f"{name} {tool}", flush=True)
            results[name][tool] = measure_dataset(
                files_dir, score_fn=score_fn, monotonic=monotonic, timeout=timeout
            )

    label_width = max(len("Dataset"), *(len(name) for name in experiment.datasets))
    for title, field, precision in (
        ("Scores", "value", 6),
        ("Evaluation time (seconds)", "seconds", 3),
    ):
        print(title)
        print(
            f"{'Dataset':<{label_width}}  "
            + "  ".join(f"{tool:>16}" for tool in score_fns)
        )
        for name, measurements in results.items():
            print(
                f"{name:<{label_width}}  "
                + "  ".join(
                    _format_cell(measurements[tool][field], precision)
                    for tool in score_fns
                )
            )
        print()

    import matplotlib

    matplotlib.use("Agg")
    import matplotlib.pyplot as plt

    fig = plot_bars(results, experiment)
    output_dir.mkdir(parents=True, exist_ok=True)
    png = output_dir / f"{experiment.id}.png"
    try:
        fig.savefig(png, dpi=180)
    finally:
        plt.close(fig)
    if not png.is_file():
        raise RuntimeError(f"PNG not written: {png}")
    return results


def plot_bars(results: dict, experiment: Experiment):
    import matplotlib.pyplot as plt

    labels = list(experiment.datasets)
    tools = list(experiment.tools)
    fig, axes = plt.subplots(
        1,
        len(labels),
        figsize=(8 * len(labels), 6),
        squeeze=False,
        constrained_layout=True,
    )
    fig.suptitle(experiment.title)
    for ax, dataset in zip(axes[0], labels):
        xs: list[int] = []
        heights: list[float] = []
        colors: list[str] = []
        for i, tool in enumerate(tools):
            value = results[dataset][tool]["value"]
            seconds = round(float(results[dataset][tool]["seconds"]))
            label = (
                f"null\n{seconds}s"
                if value is None
                else f"{float(value):.6f}\n{seconds}s"
            )
            if value is None:
                ax.annotate(
                    label,
                    (i, 0.0),
                    xytext=(0, 10),
                    textcoords="offset points",
                    ha="center",
                    fontsize=9,
                )
                continue
            xs.append(i)
            heights.append(float(value))
            colors.append(tool_color(tool, i))
            ax.annotate(
                label,
                (i, value),
                xytext=(0, 8),
                textcoords="offset points",
                ha="center",
                fontsize=9,
            )
        if xs:
            ax.bar(xs, heights, color=colors, width=0.85)
        ax.margins(x=0.2)
        ax.set_xticks(range(len(tools)), tools)
        ax.set(title=dataset, xlabel="Measure", ylabel="Score")
        ax.set_ylim(0.0, 1.18)
        ax.grid(axis="y", alpha=0.3)
    return fig
