import json
from pathlib import Path

from experiment_runner.cli import main, matrix_payload
from experiment_runner.config import Experiment


def test_matrix_payload_is_include_of_ids():
    experiments = [
        Experiment("a", "score_per_measure", "t", ("d",), ("m",)),
        Experiment("b", "score_per_measure", "t", ("d",), ("m",)),
    ]
    assert matrix_payload(experiments) == {"include": [{"id": "a"}, {"id": "b"}]}


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
    assert payload == {"include": [{"id": "ex1"}]}


def test_run_unknown_id_exits_one(tmp_path: Path, capsys):
    _layout(tmp_path)
    assert main(["run", "nope"], root=tmp_path) == 1
    assert "nope" in capsys.readouterr().err


def test_run_writes_png(tmp_path: Path, monkeypatch):
    _layout(tmp_path)

    def fake_run(experiment, root, *, output_dir, **_kwargs):
        output_dir.mkdir(parents=True, exist_ok=True)
        (output_dir / f"{experiment.id}.png").write_bytes(b"png")
        return {}

    monkeypatch.setattr(
        "experiment_runner.cli.run_score_per_measure", fake_run
    )
    assert main(["run", "ex1"], root=tmp_path) == 0
    assert (tmp_path / "output" / "ex1.png").is_file()


def test_missing_json_exits_one(tmp_path: Path, capsys):
    assert main(["matrix"], root=tmp_path) == 1
    assert "experiments.json" in capsys.readouterr().err


def test_run_dispatches_measure_per_set(tmp_path: Path, monkeypatch):
    root = tmp_path
    (root / "datasets" / "ds_one").mkdir(parents=True)
    (root / "tools" / "fake-measure").mkdir(parents=True)
    (root / "datasets" / "ds_one" / "a.txt").write_text("a")
    (root / "experiments.json").write_text(
        json.dumps(
            {
                "experiments": [
                    {
                        "id": "bars",
                        "type": "measure_per_set",
                        "title": "t",
                        "datasets": ["ds_one"],
                        "tools": ["fake-measure"],
                    }
                ]
            }
        ),
        encoding="utf-8",
    )
    called = {}

    def fake_run(experiment, _root, *, output_dir, **_kwargs):
        called["type"] = experiment.type
        output_dir.mkdir(parents=True, exist_ok=True)
        (output_dir / f"{experiment.id}.png").write_bytes(b"png")
        return {}

    monkeypatch.setattr("experiment_runner.cli.run_measure_per_set", fake_run)
    assert main(["run", "bars"], root=root) == 0
    assert called["type"] == "measure_per_set"
    assert (root / "output" / "bars.png").is_file()


def test_run_dispatches_score_for_fastr(tmp_path: Path, monkeypatch):
    root = tmp_path
    (root / "datasets" / "ds_one").mkdir(parents=True)
    (root / "tools" / "fake-measure").mkdir(parents=True)
    (root / "datasets" / "ds_one" / "a.txt").write_text("a")
    (root / "experiments.json").write_text(
        json.dumps(
            {
                "experiments": [
                    {
                        "id": "fastr",
                        "type": "score_for_fastr",
                        "title": "t",
                        "datasets": ["ds_one"],
                        "tools": ["fake-measure"],
                    }
                ]
            }
        ),
        encoding="utf-8",
    )
    called = {}

    def fake_run(experiment, _root, *, output_dir, **_kwargs):
        called["type"] = experiment.type
        output_dir.mkdir(parents=True, exist_ok=True)
        (output_dir / f"{experiment.id}.png").write_bytes(b"png")
        return {}

    monkeypatch.setattr("experiment_runner.cli.run_score_for_fastr", fake_run)
    assert main(["run", "fastr"], root=root) == 0
    assert called["type"] == "score_for_fastr"
    assert (root / "output" / "fastr.png").is_file()


def test_run_dispatches_score_for_random_filter(tmp_path: Path, monkeypatch):
    root = tmp_path
    (root / "datasets" / "ds_one").mkdir(parents=True)
    (root / "tools" / "fake-measure").mkdir(parents=True)
    (root / "datasets" / "ds_one" / "a.txt").write_text("a")
    (root / "experiments.json").write_text(
        json.dumps(
            {
                "experiments": [
                    {
                        "id": "rand",
                        "type": "score_for_random_filter",
                        "title": "t",
                        "datasets": ["ds_one"],
                        "tools": ["fake-measure"],
                    }
                ]
            }
        ),
        encoding="utf-8",
    )
    called = {}

    def fake_run(experiment, _root, *, output_dir, **_kwargs):
        called["type"] = experiment.type
        output_dir.mkdir(parents=True, exist_ok=True)
        (output_dir / f"{experiment.id}.png").write_bytes(b"png")
        return {}

    monkeypatch.setattr(
        "experiment_runner.cli.run_score_for_random_filter", fake_run
    )
    assert main(["run", "rand"], root=root) == 0
    assert called["type"] == "score_for_random_filter"
    assert (root / "output" / "rand.png").is_file()
