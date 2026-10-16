from __future__ import annotations

import os
import shutil
import tempfile
import time
from collections.abc import Callable, Mapping
from pathlib import Path

from experiment_runner.config import Experiment
from experiment_runner.paths import dataset_dir, load_score
from experiment_runner.score_per_measure import ScoreFn, measure_dataset
from experiment_runner.timeout import SCORE_TIMEOUT_SECONDS, call_timed

FASTR_ALGOS = ("FAST++", "FAST-CS")
BUDGET_PCTS = tuple(range(100, 0, -5))

ReduceFn = Callable[[Path, str, float], list[str]]


def list_basenames(files_dir: Path) -> list[str]:
    names = sorted(p.name for p in files_dir.iterdir() if p.is_file())
    if not names:
        raise ValueError(f"no files in {files_dir}")
    return names


def link_or_copy(src: Path, dest: Path) -> None:
    try:
        os.link(src, dest)
    except OSError:
        shutil.copy2(src, dest)


def stage_kept(files_dir: Path, names: list[str], dest_dir: Path) -> None:
    dest_dir.mkdir(parents=True, exist_ok=True)
    for name in names:
        src = files_dir / name
        if not src.is_file():
            raise ValueError(f"unknown kept basename: {name}")
        link_or_copy(src, dest_dir / name)


def _default_reduce(files_dir: Path, algo: str, target_percent: float) -> list[str]:
    from fast_filter import reduce

    return reduce(files_dir, algo, target_percent)


def _null_measures(tools: tuple[str, ...]) -> dict:
    return {tool: {"value": None, "seconds": 0.0} for tool in tools}


def run_score_for_fastr(
    experiment: Experiment,
    root: Path,
    *,
    score_fns: Mapping[str, ScoreFn] | None = None,
    reduce_fn: ReduceFn | None = None,
    monotonic=None,
    timeout: float = SCORE_TIMEOUT_SECONDS,
    output_dir: Path,
) -> dict:
    if score_fns is None:
        score_fns = {name: load_score(name) for name in experiment.tools}
    if reduce_fn is None:
        reduce_fn = _default_reduce
    clock = monotonic or time.monotonic
    tools = tuple(score_fns)
    results: dict = {}
    for dataset_name in experiment.datasets:
        files_dir = dataset_dir(root, dataset_name)
        all_names = list_basenames(files_dir)
        results[dataset_name] = {}
        for algo in FASTR_ALGOS:
            results[dataset_name][algo] = {}
            for pct in BUDGET_PCTS:
                if pct == 100:
                    names, reduce_seconds = all_names, None
                    in_place = True
                else:
                    t0 = clock()
                    kept = call_timed(
                        reduce_fn, (files_dir, algo, float(pct)), timeout=timeout
                    )
                    reduce_seconds = float(clock() - t0)
                    if kept is None:
                        results[dataset_name][algo][pct] = {
                            "kept_count": None,
                            "reduce_seconds": reduce_seconds,
                            "measures": _null_measures(tools),
                        }
                        print(
                            f"{dataset_name} {algo} pct={pct} kept=null "
                            + " ".join(f"{tool}=null" for tool in tools)
                        )
                        continue
                    names = list(kept)
                    in_place = False
                measures: dict = {}
                if in_place:
                    for tool, score_fn in score_fns.items():
                        measures[tool] = measure_dataset(
                            files_dir,
                            score_fn=score_fn,
                            monotonic=monotonic,
                            timeout=timeout,
                        )
                else:
                    output_dir.mkdir(parents=True, exist_ok=True)
                    with tempfile.TemporaryDirectory(
                        prefix="fastr-kept-", dir=output_dir
                    ) as tmp:
                        dest = Path(tmp) / "kept"
                        stage_kept(files_dir, names, dest)
                        for tool, score_fn in score_fns.items():
                            measures[tool] = measure_dataset(
                                dest,
                                score_fn=score_fn,
                                monotonic=monotonic,
                                timeout=timeout,
                            )
                results[dataset_name][algo][pct] = {
                    "kept_count": len(names),
                    "reduce_seconds": reduce_seconds,
                    "measures": measures,
                }
                values = " ".join(
                    (
                        f"{tool}=null"
                        if measures[tool]["value"] is None
                        else f"{tool}={measures[tool]['value']:.6f}"
                    )
                    for tool in tools
                )
                print(
                    f"{dataset_name} {algo} pct={pct} kept={len(names)} {values}"
                )

    import matplotlib

    matplotlib.use("Agg")
    import matplotlib.pyplot as plt

    fig = plot_budget_grid(results, experiment)
    output_dir.mkdir(parents=True, exist_ok=True)
    png = output_dir / f"{experiment.id}.png"
    try:
        fig.savefig(png, dpi=180)
    finally:
        plt.close(fig)
    if not png.is_file():
        raise RuntimeError(f"PNG not written: {png}")
    return results


def plot_budget_grid(results: dict, experiment: Experiment):
    import matplotlib.pyplot as plt

    datasets = list(experiment.datasets)
    tools = list(experiment.tools)
    n = len(datasets)
    fig, axes = plt.subplots(
        n,
        2,
        figsize=(10, 5 * n),
        squeeze=False,
        constrained_layout=True,
    )
    fig.suptitle(experiment.title)
    positions = list(range(len(BUDGET_PCTS)))
    labels = [str(pct) for pct in BUDGET_PCTS]
    for row, dataset in enumerate(datasets):
        for col, algo in enumerate(FASTR_ALGOS):
            ax = axes[row][col]
            for i, tool in enumerate(tools):
                ys = []
                for pct in BUDGET_PCTS:
                    value = results[dataset][algo][pct]["measures"][tool]["value"]
                    ys.append(float("nan") if value is None else float(value))
                ax.plot(positions, ys, marker="o", color=f"C{i}", label=tool)
            ax.set_title(f"{dataset} — {algo}")
            ax.set_xlabel("budget % of original suite")
            ax.set_ylabel("Score")
            ax.set_ylim(0.0, 1.0)
            ax.set_xticks(positions, labels, fontsize=8)
            ax.set_xlim(-0.5, len(BUDGET_PCTS) - 0.5)
            ax.legend(fontsize=8)
            ax.grid(axis="y", alpha=0.3)
    return fig
