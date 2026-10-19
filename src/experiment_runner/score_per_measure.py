from __future__ import annotations

import time
from collections.abc import Callable, Mapping
from pathlib import Path

from experiment_runner.config import Experiment
from experiment_runner.paths import dataset_dir, load_score
from experiment_runner.timeout import SCORE_TIMEOUT_SECONDS, call_score

ScoreFn = Callable[[Path], float]


def _format_cell(value: object, precision: int) -> str:
    if value is None:
        return f"{'null':>16}"
    return f"{float(value):>16.{precision}f}"


def measure_dataset(
    files_dir: Path,
    *,
    score_fn: ScoreFn,
    monotonic=None,
    timeout: float = SCORE_TIMEOUT_SECONDS,
) -> dict:
    clock = monotonic or time.monotonic
    t0 = clock()
    value = call_score(score_fn, files_dir, timeout=timeout)
    elapsed = clock() - t0
    return {"value": value, "seconds": float(elapsed)}


def run_score_per_measure(
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
                    _format_cell(measurements[tool][field], precision) for tool in score_fns
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
    n_datasets = len(labels)
    n_tools = len(tools)
    panel_w = max(5.0, 0.9 * n_datasets)
    panel_h = max(5.0, 4.5 + 0.12 * n_datasets)
    fig, axes = plt.subplots(
        1,
        n_tools,
        figsize=(panel_w * n_tools, panel_h),
        squeeze=False,
        constrained_layout=True,
    )
    fig.suptitle(experiment.title)
    colors = [f"C{i}" for i in range(len(labels))]
    for ax, tool in zip(axes[0], tools):
        xs: list[float] = []
        ys: list[float] = []
        point_colors: list[str] = []
        for x, label in enumerate(labels):
            value = results[label][tool]["value"]
            if value is None:
                ax.annotate(
                    "null",
                    (x, 0.0),
                    xytext=(0, 10),
                    textcoords="offset points",
                    ha="center",
                    fontsize=9,
                )
                continue
            xs.append(float(x))
            ys.append(float(value))
            point_colors.append(colors[x])
            ax.annotate(
                f"{float(value):.6f}",
                (x, value),
                xytext=(0, 10),
                textcoords="offset points",
                ha="center",
                fontsize=9,
            )
        if xs:
            ax.scatter(xs, ys, c=point_colors, s=70, zorder=3)
        ax.set_xticks(
            range(len(labels)),
            labels,
            rotation=25,
            ha="right",
            fontsize=9,
        )
        ax.set(title=tool, xlabel="Dataset", ylabel="Score")
        ax.set_ylim(0.0, 1.18)
        ax.margins(x=0.15)
        ax.grid(axis="y", alpha=0.3)
    return fig
