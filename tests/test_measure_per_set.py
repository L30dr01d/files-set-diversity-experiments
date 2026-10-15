from pathlib import Path

from experiment_runner.config import Experiment
from experiment_runner.measure_per_set import plot_bars, run_measure_per_set
from experiment_runner.timeout import hang_score, raise_score


def test_run_prints_tables_and_writes_png(tmp_path: Path, capsys) -> None:
    root = tmp_path / "repo"
    first = root / "datasets" / "ds_one"
    second = root / "datasets" / "ds_two"
    first.mkdir(parents=True)
    second.mkdir(parents=True)
    (first / "a.txt").write_text("a")
    (second / "a.txt").write_text("aa")
    output_dir = tmp_path / "output"
    experiment = Experiment(
        id="bars",
        type="measure_per_set",
        title="Viewer title",
        datasets=("ds_one", "ds_two"),
        tools=("fake-metric", "other-metric"),
    )
    ticks = iter(range(20))
    result = run_measure_per_set(
        experiment,
        root,
        score_fns={
            "fake-metric": lambda path: 0.1 if path.name == "ds_one" else 0.2,
            "other-metric": lambda path: 0.3 if path.name == "ds_one" else 0.4,
        },
        monotonic=lambda: next(ticks),
        output_dir=output_dir,
    )
    assert result == {
        "ds_one": {
            "fake-metric": {"value": 0.1, "seconds": 1.0},
            "other-metric": {"value": 0.3, "seconds": 1.0},
        },
        "ds_two": {
            "fake-metric": {"value": 0.2, "seconds": 1.0},
            "other-metric": {"value": 0.4, "seconds": 1.0},
        },
    }
    png = output_dir / "bars.png"
    assert png.is_file()
    assert png.stat().st_size > 0
    out = capsys.readouterr().out
    assert "Scores" in out
    assert "Evaluation time (seconds)" in out
    assert "ds_one" in out and "ds_two" in out


def test_plot_one_bar_panel_per_dataset() -> None:
    import matplotlib

    matplotlib.use("Agg")
    import matplotlib.pyplot as plt

    experiment = Experiment(
        id="bars",
        type="measure_per_set",
        title="Viewer title",
        datasets=("ds_one", "ds_two"),
        tools=("fake-metric", "other-metric"),
    )
    results = {
        "ds_one": {
            "fake-metric": {"value": 0.25, "seconds": 1.25},
            "other-metric": {"value": 0.40, "seconds": 2.5},
        },
        "ds_two": {
            "fake-metric": {"value": 0.35, "seconds": 0.5},
            "other-metric": {"value": 0.50, "seconds": 3.0},
        },
    }
    fig = plot_bars(results, experiment)
    try:
        assert fig._suptitle.get_text() == "Viewer title"
        assert len(fig.axes) == 2
        for ax, dataset, expected in zip(
            fig.axes,
            ("ds_one", "ds_two"),
            (
                [(0.25, 1.25), (0.40, 2.5)],
                [(0.35, 0.5), (0.50, 3.0)],
            ),
        ):
            assert ax.get_title() == dataset
            assert ax.get_xlabel() == "Metric"
            assert ax.get_ylabel() == "Score"
            assert ax.get_ylim() == (0.0, 1.18)
            assert [tick.get_text() for tick in ax.get_xticklabels()] == [
                "fake-metric",
                "other-metric",
            ]
            assert [patch.get_height() for patch in ax.patches] == [
                value for value, _seconds in expected
            ]
            assert [text.get_text() for text in ax.texts] == [
                f"{value:.6f}\n{round(seconds)}s" for value, seconds in expected
            ]
        assert tuple(fig.get_size_inches()) == (16.0, 6.0)
    finally:
        plt.close(fig)


def test_plot_annotates_null_and_skips_timed_out_bar() -> None:
    import matplotlib

    matplotlib.use("Agg")
    import matplotlib.pyplot as plt

    experiment = Experiment(
        id="bars",
        type="measure_per_set",
        title="Viewer title",
        datasets=("ds_one",),
        tools=("fake-metric", "hang-metric"),
    )
    results = {
        "ds_one": {
            "fake-metric": {"value": 0.25, "seconds": 1.0},
            "hang-metric": {"value": None, "seconds": 1200.0},
        },
    }
    fig = plot_bars(results, experiment)
    try:
        ax = fig.axes[0]
        assert [patch.get_height() for patch in ax.patches] == [0.25]
        texts = [text.get_text() for text in ax.texts]
        assert "0.250000\n1s" in texts
        assert "null\n1200s" in texts
        assert fig.get_size_inches()[0] >= 8.0
    finally:
        plt.close(fig)


def test_run_prints_progress_before_each_score(tmp_path: Path, capsys) -> None:
    root = tmp_path / "repo"
    dataset = root / "datasets" / "ds_one"
    dataset.mkdir(parents=True)
    (dataset / "a.txt").write_text("a")
    experiment = Experiment(
        id="bars",
        type="measure_per_set",
        title="Viewer title",
        datasets=("ds_one",),
        tools=("fake-metric", "other-metric"),
    )
    run_measure_per_set(
        experiment,
        root,
        score_fns={
            "fake-metric": lambda path: 0.1,
            "other-metric": lambda path: 0.2,
        },
        output_dir=tmp_path / "output",
    )
    out = capsys.readouterr().out
    assert "ds_one fake-metric" in out
    assert "ds_one other-metric" in out


def test_run_prints_null_for_timed_out_score(tmp_path: Path, capsys) -> None:
    root = tmp_path / "repo"
    dataset = root / "datasets" / "ds_one"
    dataset.mkdir(parents=True)
    (dataset / "a.txt").write_text("a")
    experiment = Experiment(
        id="bars",
        type="measure_per_set",
        title="Viewer title",
        datasets=("ds_one",),
        tools=("hang-metric",),
    )
    run_measure_per_set(
        experiment,
        root,
        score_fns={"hang-metric": hang_score},
        timeout=0.5,
        output_dir=tmp_path / "output",
    )
    assert "null" in capsys.readouterr().out


def test_run_continues_when_one_metric_raises(tmp_path: Path, capsys) -> None:
    root = tmp_path / "repo"
    dataset = root / "datasets" / "ds_one"
    dataset.mkdir(parents=True)
    (dataset / "a.txt").write_text("a")
    output_dir = tmp_path / "output"
    experiment = Experiment(
        id="bars",
        type="measure_per_set",
        title="Viewer title",
        datasets=("ds_one",),
        tools=("boom-metric", "ok-metric"),
    )
    result = run_measure_per_set(
        experiment,
        root,
        score_fns={"boom-metric": raise_score, "ok-metric": lambda path: 0.5},
        output_dir=output_dir,
    )
    assert result["ds_one"]["boom-metric"]["value"] is None
    assert result["ds_one"]["ok-metric"]["value"] == 0.5
    assert (output_dir / "bars.png").is_file()
    captured = capsys.readouterr()
    assert "warning:" in captured.err
    assert "null" in captured.out
