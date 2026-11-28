import json
import pytest
from pathlib import Path

from experiment_runner.cli import main, matrix_payload
from experiment_runner.config import Experiment


def test_matrix_payload_is_include_of_ids():
    experiments = [
        Experiment("a", "score_per_measure", "t", ("d",), ("m",)),
        Experiment("b", "score_per_measure", "t", ("d",), ("m",)),
    ]
    assert matrix_payload(experiments) == {
        "include": [
            {"id": "a", "type": "score_per_measure"},
            {"id": "b", "type": "score_per_measure"},
        ]
    }


def _layout(root: Path) -> None:
    (root / "datasets" / "ds_one").mkdir(parents=True)
    (root / "tools" / "fake-measure").mkdir(parents=True)
    (root / "datasets" / "ds_one" / "a.txt").write_text("a")
    (root / "experiments.json").write_text(
        json.dumps(
            {
                "experiments": [
                    {
                        "id": "ex1",
                        "type": "score_per_measure",
                        "title": "Viewer title",
                        "datasets": ["ds_one"],
                        "tools": ["fake-measure"],
                    }
                ]
            }
        ),
        encoding="utf-8",
    )


def test_matrix_cli_prints_include(tmp_path: Path, capsys):
    _layout(tmp_path)
    assert main(["matrix"], root=tmp_path) == 0
    payload = json.loads(capsys.readouterr().out)
    assert payload == {"include": [{"id": "ex1", "type": "score_per_measure"}]}


def test_run_unknown_id_exits_one(tmp_path: Path, capsys):
    _layout(tmp_path)
    assert main(["run", "nope"], root=tmp_path) == 1
    assert "nope" in capsys.readouterr().err


def test_missing_json_exits_one(tmp_path: Path, capsys):
    assert main(["matrix"], root=tmp_path) == 1
    assert "experiments.json" in capsys.readouterr().err


@pytest.mark.parametrize(("kind", "columns"), [
    ("score_per_measure", ["fake-measure"]),
    ("measure_per_set", ["fake-measure"]),
    ("score_for_fastr", ["FAST++", "FAST-CS"]),
    ("score_for_random_filter", ["fake-measure"]),
    ("score_for_panhard_dpi", ["fake-measure"]),
    ("score_for_panhard_rni", ["fake-measure"]),
    ("coverage_with_filter", ["coverage"]),
    ("coverage_with_filter_panhard_dpi", ["coverage"]),
    ("coverage_with_filter_panhard_rni", ["coverage"]),
])
def test_whole_experiment_workers_write_common_records(tmp_path, monkeypatch, kind, columns):
    _layout(tmp_path)
    config = tmp_path / "experiments.json"
    payload = json.loads(config.read_text())
    payload["experiments"][0]["type"] = kind
    config.write_text(json.dumps(payload))
    monkeypatch.setattr("experiment_runner.worker.compute_cell", lambda *args: None)
    results = tmp_path / "results"
    assert main(["worker", "ex1", "--results-dir", str(results)], root=tmp_path) == 0
    records = [json.loads(file.read_text()) for file in sorted(results.rglob("*.json"))]
    assert records == [dict(experiment="ex1", cluster=0, dataset="ds_one", column=col, payload=None)
                       for col in columns]
    assert all(p.suffix == ".json" for p in results.rglob("*") if p.is_file())
    assert main(["aggregate", "--results-dir", str(results), "--output-dir", str(tmp_path/"plots")], root=tmp_path) == 0
    assert (tmp_path/"plots/ex1.html").is_file()


def test_disabled_experiment_is_excluded_from_matrix_but_runs_manually(tmp_path, monkeypatch, capsys):
    _layout(tmp_path)
    config = tmp_path / "experiments.json"
    payload = json.loads(config.read_text())
    payload["experiments"][0]["disable_reason"] = "Temporarily too slow"
    config.write_text(json.dumps(payload))
    assert main(["matrix"], root=tmp_path) == 0
    assert json.loads(capsys.readouterr().out) == {"include": []}
    called = []
    monkeypatch.setattr("experiment_runner.worker.compute_cell", lambda exp, *args: called.append(exp.id))
    assert main(["run", "ex1"], root=tmp_path) == 0
    assert called == ["ex1"]
    assert (tmp_path/"output/ex1.html").is_file()


def test_matrix_rejects_invalid_disable_reasons(tmp_path, capsys):
    _layout(tmp_path)
    config = tmp_path / "experiments.json"
    payload = json.loads(config.read_text())
    for reason in [None, "", "  ", False, 42]:
        payload["experiments"][0]["disable_reason"] = reason
        config.write_text(json.dumps(payload))
        assert main(["matrix"], root=tmp_path) == 1
        assert "disable_reason" in capsys.readouterr().err
