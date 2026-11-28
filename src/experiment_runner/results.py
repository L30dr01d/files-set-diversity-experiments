"""Per-cell checkpoints. Artifact downloads may introduce an enclosing directory."""

import json
import math
from hashlib import sha256
from pathlib import Path
from tempfile import NamedTemporaryFile

from .config import Experiment


def subset_digest(paths):
    names = sorted(p.name for p in paths)
    return sha256(json.dumps(names, ensure_ascii=True).encode()).hexdigest()


def write_cell(
    directory: Path,
    experiment: Experiment,
    index: int,
    dataset: str,
    column: str,
    payload: dict | None,
) -> None:
    cluster = experiment.clusters[index]
    position = cluster.datasets.index(dataset) * len(cluster.tools or ("coverage",))
    position += (cluster.tools or ("coverage",)).index(column)
    target = directory / experiment.id / f"{index}-{position}.json"
    target.parent.mkdir(parents=True, exist_ok=True)
    record = dict(
        experiment=experiment.id,
        cluster=index,
        dataset=dataset,
        column=column,
        payload=payload,
    )
    with NamedTemporaryFile("w", dir=target.parent, delete=False, suffix=".tmp") as f:
        json.dump(record, f, allow_nan=False)
    Path(f.name).replace(target)


def validate_payload(experiment, column, data):
    if data is None:
        return

    def score(measure):
        value = measure["value"]
        if value is not None and (
            type(value) not in (int, float) or not math.isfinite(value)
        ):
            raise ValueError("invalid score value")

    kind = experiment.type
    if kind in ("score_per_measure", "measure_per_set"):
        score(data)
    elif kind == "score_for_fastr":
        from .score_for_fastr import BUDGET_PCTS

        for budget in BUDGET_PCTS:
            for scorer in experiment.scorers:
                score(data[str(budget)]["measures"][scorer])
    elif kind == "coverage_with_filter":
        from .coverage_with_filter import BUDGET_PERCENTS, PLOT_ROWS

        for tool, _, _ in PLOT_ROWS:
            for metric in ("line", "mcdc", "joint"):
                for count in data["adequacy"][tool][metric]:
                    if not 0 <= count <= data["dataset_size"]:
                        raise ValueError("invalid adequacy count")
            if tool != "both":
                for pct in BUDGET_PERCENTS:
                    for draw in data["budgets"][tool][str(pct)]:
                        for metric in ("line", "mcdc"):
                            float(draw[metric])
    else:
        runs = data["runs"] if kind == "score_for_random_filter" else [data]
        for run in runs:
            for step in run["steps"] or ():
                int(step["remaining_count"])
                if kind.startswith("coverage_"):
                    float(step["score"])
                    float(step["residual"])
                    for measurements in step["coverage"].values():
                        float(measurements["line"])
                        float(measurements["mcdc"])
                else:
                    score(step["measures"][column])


def collect_cells(experiment: Experiment, directory: Path) -> dict:
    expected = {
        cell: i
        for i, cluster in enumerate(experiment.clusters)
        for cell in cluster.cells()
    }
    found = {}
    for path in directory.glob(f"**/{experiment.id}/*.json"):
        record = json.loads(path.read_text())
        key = (record["dataset"], record["column"])
        if (
            record["experiment"] != experiment.id
            or key not in expected
            or record["cluster"] != expected[key]
        ):
            raise ValueError(f"unexpected result coordinates in {path}")
        value = record["payload"]
        if value is not None and not isinstance(value, dict):
            raise ValueError(f"invalid result in {path}")
        try:
            validate_payload(experiment, key[1], value)
        except (KeyError, TypeError, AttributeError, ValueError) as exc:
            raise ValueError(f"invalid payload in {path}: {exc}") from exc
        if key in found and value != found[key]:
            raise ValueError(f"conflicting result for {key} in {path}")
        found[key] = value
    return {key: found.get(key) for key in expected}
