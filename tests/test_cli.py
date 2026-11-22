import json
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


def test_run_dispatches_coverage_with_filter(tmp_path: Path, monkeypatch):
    root = tmp_path
    (root / "datasets" / "ds_one").mkdir(parents=True)
    (root / "tools" / "fake-measure").mkdir(parents=True)
    (root / "datasets" / "ds_one" / "a.txt").write_text("a")
    (root / "experiments.json").write_text(
        json.dumps(
            {
                "experiments": [
                    {
                        "id": "coverage",
                        "type": "coverage_with_filter",
                        "title": "t",
                        "datasets": ["ds_one"],
                        "tools": ["fake-measure"],
                    }
                ]
            }
        ),
        encoding="utf-8",
    )
    called = {"coverage": 0, "fastr": 0}

    def fake_coverage(experiment, _root, *, output_dir, **_kwargs):
        called["coverage"] += 1
        output_dir.mkdir(parents=True, exist_ok=True)
        (output_dir / f"{experiment.id}.png").write_bytes(b"png")
        return {}

    def fake_fastr(*_args, **_kwargs):
        called["fastr"] += 1
        return {}

    monkeypatch.setattr(
        "experiment_runner.cli.run_coverage_with_filter", fake_coverage
    )
    monkeypatch.setattr("experiment_runner.cli.run_score_for_fastr", fake_fastr)
    assert main(["run", "coverage"], root=root) == 0
    assert called["coverage"] == 1
    assert called["fastr"] == 0
    assert (root / "output" / "coverage.png").is_file()


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


def test_disabled_experiment_is_excluded_from_matrix_but_runs_manually(tmp_path, monkeypatch, capsys):
    _layout(tmp_path)
    config = tmp_path / "experiments.json"
    payload = json.loads(config.read_text())
    payload["experiments"][0]["disable_reason"] = "Temporarily too slow"
    config.write_text(json.dumps(payload))
    assert main(["matrix"], root=tmp_path) == 0
    assert json.loads(capsys.readouterr().out) == {"include": []}
    called = []
    monkeypatch.setattr("experiment_runner.cli.run_score_per_measure", lambda exp, *args, **kwargs: called.append(exp.id))
    assert main(["run", "ex1"], root=tmp_path) == 0
    assert called == ["ex1"]


def test_matrix_rejects_invalid_disable_reasons(tmp_path, capsys):
    _layout(tmp_path)
    config = tmp_path / "experiments.json"
    payload = json.loads(config.read_text())
    for reason in [None, "", "  ", False, 42]:
        payload["experiments"][0]["disable_reason"] = reason
        config.write_text(json.dumps(payload))
        assert main(["matrix"], root=tmp_path) == 1
        assert "disable_reason" in capsys.readouterr().err


def test_panhard_coverage_types_dispatch_by_ranking(tmp_path, monkeypatch, capsys):
    from experiment_runner import cli

    datasets = ["first", "second"]
    for dataset in datasets:
        (tmp_path / "datasets" / dataset).mkdir(parents=True)
    types = ["coverage_with_filter_panhard_dpi", "coverage_with_filter_panhard_rni"]
    records = [
        {"id": ranking, "type": kind, "title": ranking, "datasets": datasets, "tools": []}
        for ranking, kind in zip(("dpi", "rni"), types)
    ]
    (tmp_path / "experiments.json").write_text(json.dumps({"experiments": records}))
    calls = []

    def run(experiment, root, *, ranking, output_dir):
        calls.append((experiment.datasets, experiment.tools, root, ranking, output_dir))

    monkeypatch.setattr(cli, "run_coverage_with_filter_panhard", run)
    assert main(["matrix"], root=tmp_path) == 0
    assert [row["type"] for row in json.loads(capsys.readouterr().out)["include"]] == types
    for ranking in ("dpi", "rni"):
        assert main(["run", ranking], root=tmp_path) == 0
    assert calls == [
        (tuple(datasets), (), tmp_path, ranking, tmp_path / "output")
        for ranking in ("dpi", "rni")
    ]
