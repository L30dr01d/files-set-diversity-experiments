import pytest
from experiment_runner.config import Cluster, Experiment
from experiment_runner.results import collect_cells, write_cell


def test_retry_missing_and_zero(tmp_path):
    exp = Experiment(
        "example",
        "score_per_measure",
        "Example",
        ("a", "b"),
        ("x",),
        clusters=(Cluster(("a", "b"), ("x",)),),
    )
    for attempt in ("first", "second"):
        write_cell(tmp_path / attempt, exp, 0, "a", "x", {"value": 0})
    assert collect_cells(exp, tmp_path) == {("a", "x"): {"value": 0}, ("b", "x"): None}
    write_cell(tmp_path / "second", exp, 0, "a", "x", {"value": 1})
    with pytest.raises(ValueError, match="conflicting"):
        collect_cells(exp, tmp_path)


def test_malformed_score_cannot_become_silent_gap(tmp_path):
    exp = Experiment(
        "x",
        "score_per_measure",
        "X",
        ("d",),
        ("t",),
        clusters=(Cluster(("d",), ("t",)),),
    )
    write_cell(tmp_path, exp, 0, "d", "t", {})
    with pytest.raises(ValueError, match="payload"):
        collect_cells(exp, tmp_path)
