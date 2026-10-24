from pathlib import Path
from xml.etree import ElementTree

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
        tools=("fake-measure", "other-measure"),
    )
    ticks = iter(range(20))
    result = run_measure_per_set(
        experiment,
        root,
        score_fns={
            "fake-measure": lambda path: 0.1 if path.name == "ds_one" else 0.2,
            "other-measure": lambda path: 0.3 if path.name == "ds_one" else 0.4,
        },
        monotonic=lambda: next(ticks),
        output_dir=output_dir,
    )
    assert result == {
        "ds_one": {
            "fake-measure": {"value": 0.1, "seconds": 1.0},
            "other-measure": {"value": 0.3, "seconds": 1.0},
        },
        "ds_two": {
            "fake-measure": {"value": 0.2, "seconds": 1.0},
            "other-measure": {"value": 0.4, "seconds": 1.0},
        },
    }
    png = output_dir / "bars.png"
    assert png.is_file()
    assert png.stat().st_size > 0
    assert (
        ElementTree.parse(png.with_suffix(".svg")).getroot().tag
        == "{http://www.w3.org/2000/svg}svg"
    )
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
        tools=("fake-measure", "other-measure"),
    )
    results = {
        "ds_one": {
            "fake-measure": {"value": 0.25, "seconds": 1.25},
            "other-measure": {"value": 0.40, "seconds": 2.5},
        },
        "ds_two": {
            "fake-measure": {"value": 0.35, "seconds": 0.5},
            "other-measure": {"value": 0.50, "seconds": 3.0},
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
            assert ax.get_xlabel() == "Measure"
            assert ax.get_ylabel() == "Score"
            assert ax.get_ylim() == (0.0, 1.18)
            assert [tick.get_text() for tick in ax.get_xticklabels()] == [
                "fake-measure",
                "other-measure",
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


def test_plot_bars_uses_pinned_measure_colors() -> None:
    import matplotlib

    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    from matplotlib.colors import to_rgba

    experiment = Experiment(
        id="bars",
        type="measure_per_set",
        title="Viewer title",
        datasets=("ds_one",),
        tools=("levassor-measure", "panhard-v3-measure"),
    )
    results = {
        "ds_one": {
            "levassor-measure": {"value": 0.25, "seconds": 1.0},
            "panhard-v3-measure": {"value": 0.40, "seconds": 1.0},
        },
    }
    fig = plot_bars(results, experiment)
    try:
        colors = [patch.get_facecolor() for patch in fig.axes[0].patches]
        assert to_rgba(colors[0]) == to_rgba("C1")
        assert to_rgba(colors[1]) == to_rgba("C0")
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
        tools=("fake-measure", "hang-measure"),
    )
    results = {
        "ds_one": {
            "fake-measure": {"value": 0.25, "seconds": 1.0},
            "hang-measure": {"value": None, "seconds": 1200.0},
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
        tools=("fake-measure", "other-measure"),
    )
    run_measure_per_set(
        experiment,
        root,
        score_fns={
            "fake-measure": lambda path: 0.1,
            "other-measure": lambda path: 0.2,
        },
        output_dir=tmp_path / "output",
    )
    out = capsys.readouterr().out
    assert "ds_one fake-measure" in out
    assert "ds_one other-measure" in out


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
        tools=("hang-measure",),
    )
    run_measure_per_set(
        experiment,
        root,
        score_fns={"hang-measure": hang_score},
        timeout=0.5,
        output_dir=tmp_path / "output",
    )
    assert "null" in capsys.readouterr().out


def test_run_continues_when_one_measure_raises(tmp_path: Path, capsys) -> None:
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
        tools=("boom-measure", "ok-measure"),
    )
    result = run_measure_per_set(
        experiment,
        root,
        score_fns={"boom-measure": raise_score, "ok-measure": lambda path: 0.5},
        output_dir=output_dir,
    )
    assert result["ds_one"]["boom-measure"]["value"] is None
    assert result["ds_one"]["ok-measure"]["value"] == 0.5
    assert (output_dir / "bars.png").is_file()
    captured = capsys.readouterr()
    assert "warning:" in captured.err
    assert "null" in captured.out
