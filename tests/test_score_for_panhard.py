import json
from pathlib import Path

from experiment_runner.config import Experiment
from experiment_runner.plotting import tool_color
from experiment_runner.score_for_panhard import plot_panhard_grid, run_score_for_panhard
from panhard_filter import FilterResult, FilterStep


def _experiment() -> Experiment:
    return Experiment(
        id="panhard_plot",
        type="score_for_panhard",
        title="Panhard",
        datasets=("ds_one",),
        tools=("panhard-measure", "levassor-measure"),
    )


def test_reuses_panhard_scores_and_scores_other_tools(tmp_path: Path):
    def stub_filter(paths, *, dont_stop):
        assert dont_stop is True
        current = [Path(p) for p in paths]
        steps = []
        while True:
            score = 0.2 if len(current) == 2 else 0.5
            steps.append(FilterStep(len(current), score, tuple(current)))
            if len(current) <= 2:
                break
            current = current[:-1]
        return FilterResult(kept=list(steps[-1].remaining), steps=steps, stop_count=2)

    root = tmp_path / "repo"
    files = root / "datasets" / "ds_one"
    files.mkdir(parents=True)
    for name in ("a.txt", "b.txt", "c.txt"):
        (files / name).write_text(name)
    seen: list[list[str]] = []
    panhard_calls: list[Path] = []

    def panhard_score(path: Path) -> float:
        panhard_calls.append(path)
        return 1.0

    def levassor(path: Path) -> float:
        seen.append(sorted(p.name for p in path.iterdir() if p.is_file()))
        return 0.4

    result = run_score_for_panhard(
        _experiment(),
        root,
        score_fns={"panhard-measure": panhard_score, "levassor-measure": levassor},
        filter_fn=stub_filter,
        output_dir=tmp_path / "output",
    )
    steps = result["ds_one"]["steps"]
    assert panhard_calls == []
    assert [step["measures"]["panhard-measure"]["value"] for step in steps] == [0.5, 0.2]
    assert seen == [["a.txt", "b.txt", "c.txt"], ["a.txt", "b.txt"]]
    assert result["ds_one"]["stop_count"] == 2
    assert (tmp_path / "output" / "panhard_plot.png").is_file()


def test_includes_panhard_scores_without_listing_the_tool(tmp_path: Path):
    def stub_filter(paths, *, dont_stop):
        current = [Path(p) for p in paths]
        steps = [FilterStep(len(current), 0.5, tuple(current))]
        current = current[:-1]
        steps.append(FilterStep(len(current), 0.2, tuple(current)))
        return FilterResult(kept=list(steps[-1].remaining), steps=steps, stop_count=2)

    root = tmp_path / "repo"
    files = root / "datasets" / "ds_one"
    files.mkdir(parents=True)
    for name in ("a.txt", "b.txt"):
        (files / name).write_text(name)
    experiment = Experiment(
        id="x",
        type="score_for_panhard",
        title="t",
        datasets=("ds_one",),
        tools=("levassor-measure",),
    )
    result = run_score_for_panhard(
        experiment,
        root,
        score_fns={"levassor-measure": lambda path: 0.4},
        filter_fn=stub_filter,
        output_dir=tmp_path / "out",
    )
    steps = result["ds_one"]["steps"]
    assert [step["measures"]["panhard-measure"]["value"] for step in steps] == [0.5, 0.2]
    assert [step["measures"]["levassor-measure"]["value"] for step in steps] == [0.4, 0.4]


def test_plot_always_includes_panhard_measure():
    experiment = Experiment(
        id="x",
        type="score_for_panhard",
        title="t",
        datasets=("ds_one",),
        tools=("levassor-measure",),
    )
    results = {
        "ds_one": {
            "stop_count": 2,
            "steps": [
                {
                    "remaining_count": 3,
                    "measures": {
                        "panhard-measure": {"value": 0.5},
                        "levassor-measure": {"value": 0.4},
                    },
                },
                {
                    "remaining_count": 2,
                    "measures": {
                        "panhard-measure": {"value": 0.2},
                        "levassor-measure": {"value": 0.4},
                    },
                },
            ],
        }
    }
    fig = plot_panhard_grid(results, experiment)
    labels = [line.get_label() for line in fig.axes[0].lines]
    assert "panhard-measure" in labels
    assert "levassor-measure" in labels


def test_plot_colors_and_stop_line():
    experiment = _experiment()
    results = {
        "ds_one": {
            "stop_count": 2,
            "steps": [
                {
                    "remaining_count": 3,
                    "measures": {
                        "panhard-measure": {"value": 0.5},
                        "levassor-measure": {"value": 0.4},
                    },
                },
                {
                    "remaining_count": 2,
                    "measures": {
                        "panhard-measure": {"value": 0.2},
                        "levassor-measure": {"value": 0.4},
                    },
                },
            ],
        }
    }
    fig = plot_panhard_grid(results, experiment)
    ax = fig.axes[0]
    by_label = {line.get_label(): line for line in ax.lines}
    assert by_label["panhard-measure"].get_color() == tool_color("panhard-measure", 0)
    assert by_label["levassor-measure"].get_color() == tool_color("levassor-measure", 1)
    stop = by_label["panhard stop"]
    assert list(stop.get_xdata()) == [1, 1]
    assert ax.get_xlabel() == "files count"
    assert [tick.get_text() for tick in ax.get_xticklabels()] == ["3", "2"]


def test_cli_dispatches(tmp_path: Path, monkeypatch):
    from experiment_runner.cli import main

    root = tmp_path
    (root / "datasets" / "ds_one").mkdir(parents=True)
    (root / "tools" / "panhard-measure").mkdir(parents=True)
    (root / "experiments.json").write_text(
        json.dumps(
            {
                "experiments": [
                    {
                        "id": "ph",
                        "type": "score_for_panhard",
                        "title": "t",
                        "datasets": ["ds_one"],
                        "tools": ["panhard-measure"],
                    }
                ]
            }
        ),
        encoding="utf-8",
    )

    def fake_run(experiment, _root, *, output_dir, **_kwargs):
        output_dir.mkdir(parents=True, exist_ok=True)
        (output_dir / f"{experiment.id}.png").write_bytes(b"png")
        return {}

    monkeypatch.setattr("experiment_runner.cli.run_score_for_panhard", fake_run)
    assert main(["run", "ph"], root=root) == 0
    assert (root / "output" / "ph.png").is_file()
