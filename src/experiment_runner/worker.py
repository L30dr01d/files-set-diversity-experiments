import sys
from dataclasses import replace
from pathlib import Path
from tempfile import TemporaryDirectory

from .config import ConfigError, Experiment
from .coverage_with_filter import run_coverage_with_filter
from .coverage_with_filter_panhard import run_coverage_with_filter_panhard
from .paths import dataset_dir, load_score
from .results import write_cell
from .score_for_fastr import run_score_for_fastr
from .score_for_panhard import run_score_for_panhard
from .score_for_random_filter import run_score_for_random_filter
from .score_per_measure import measure_dataset


def compute_cell(exp, dataset, column, root, scratch):
    cell = replace(exp, datasets=(dataset,), tools=(column,))
    options = dict(output_dir=scratch, render=False)
    if exp.type in ("score_per_measure", "measure_per_set"):
        return measure_dataset(dataset_dir(root, dataset), score_fn=load_score(column))
    if exp.type == "score_for_fastr":
        cell = replace(cell, tools=exp.scorers)
        return run_score_for_fastr(cell, root, algorithms=(column,), **options)[
            dataset
        ][column]
    if exp.type == "score_for_random_filter":
        cell = replace(
            cell, tools=tuple(dict.fromkeys((exp.filter_tool or exp.tools[0], column)))
        )
        return run_score_for_random_filter(cell, root, **options)[dataset]
    if exp.type == "coverage_with_filter":
        return run_coverage_with_filter(cell, root, **options)
    ranking = exp.type.rsplit("_", 1)[1]
    runner = (
        run_coverage_with_filter_panhard
        if exp.type.startswith("coverage_")
        else run_score_for_panhard
    )
    return runner(cell, root, ranking=ranking, **options)[dataset]


def run_worker(exp: Experiment, index: int, root: Path, directory: Path) -> None:
    for dataset, column in exp.clusters[index].cells():
        try:
            with TemporaryDirectory() as scratch:
                result = compute_cell(exp, dataset, column, root, Path(scratch))
        except (ConfigError, ImportError):
            raise
        except Exception as exc:
            print(
                f"{exp.id} / {dataset} / {column}: {exc}", file=sys.stderr, flush=True
            )
            result = None
        write_cell(directory, exp, index, dataset, column, result)
