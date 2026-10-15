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
    (root / "tools" / "fake-metric").mkdir(parents=True)
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
                        "tools": ["fake-metric"],
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
