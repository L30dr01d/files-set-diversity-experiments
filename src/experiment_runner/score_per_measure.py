from __future__ import annotations

import time
from collections.abc import Callable, Mapping
from pathlib import Path

from experiment_runner.config import Experiment
from experiment_runner.paths import dataset_dir, load_score

ScoreFn = Callable[[Path], float]


def measure_dataset(
    files_dir: Path,
    *,
    score_fn: ScoreFn,
    monotonic=None,
) -> dict:
    clock = monotonic or time.monotonic
    t0 = clock()
    value = float(score_fn(files_dir))
    elapsed = clock() - t0
    return {"value": value, "seconds": float(elapsed)}


def run_score_per_measure(
    experiment: Experiment,
    root: Path,
    *,
    score_fns: Mapping[str, ScoreFn] | None = None,
    monotonic=None,
    output_dir: Path,
) -> dict:
    if score_fns is None:
        score_fns = {name: load_score(name) for name in experiment.tools}
    results: dict = {}
    for name in experiment.datasets:
        files_dir = dataset_dir(root, name)
        results[name] = {}
        for tool, score_fn in score_fns.items():
            results[name][tool] = measure_dataset(
                files_dir, score_fn=score_fn, monotonic=monotonic
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
                    f"{measurements[tool][field]:>16.{precision}f}" for tool in score_fns
                )
            )
        print()

    import matplotlib

    matplotlib.use("Agg")
    import matplotlib.pyplot as plt

    fig = plot_scores(results, experiment)
    output_dir.mkdir(parents=True, exist_ok=True)
    png = output_dir / f"{experiment.id}.png"
    try:
        fig.savefig(png, dpi=180)
    finally:
        plt.close(fig)
    if not png.is_file():
        raise RuntimeError(f"PNG not written: {png}")
    return results


def plot_scores(results: dict, experiment: Experiment):
    import matplotlib.pyplot as plt

    labels = list(experiment.datasets)
    tools = list(experiment.tools)
    fig, axes = plt.subplots(
        1, len(tools), figsize=(5 * len(tools), 5), squeeze=False, constrained_layout=True
    )
    fig.suptitle(experiment.title)
    colors = [f"C{i}" for i in range(len(labels))]
    for ax, tool in zip(axes[0], tools):
        values = [results[label][tool]["value"] for label in labels]
        ax.scatter(range(len(labels)), values, c=colors, s=70, zorder=3)
        for x, value in enumerate(values):
            ax.annotate(
                f"{value:.6f}",
                (x, value),
                xytext=(0, 10),
                textcoords="offset points",
                ha="center",
                fontsize=9,
            )
        ax.set_xticks(
            range(len(labels)),
            labels,
            rotation=25,
            ha="right",
            fontsize=9,
        )
        ax.set(title=tool, xlabel="Dataset", ylabel="Score")
        ax.set_ylim(0.0, 1.0)
        ax.margins(x=0.15, y=0.25)
        ax.grid(axis="y", alpha=0.3)
    return fig
