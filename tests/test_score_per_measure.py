import time
from pathlib import Path
from xml.etree import ElementTree

import pytest

from experiment_runner.config import Experiment
from experiment_runner.score_per_measure import (
    measure_dataset,
    plot_scores,
    run_score_per_measure,
)
from experiment_runner.timeout import hang_score


def test_measure_dataset_times_injected_score(tmp_path: Path) -> None:
    ticks = iter([10.0, 10.25])
    measured = measure_dataset(
        tmp_path, score_fn=lambda path: 0.4, monotonic=lambda: next(ticks)
    )
    assert measured == {"value": 0.4, "seconds": 0.25}


def test_measure_dataset_timeout_returns_null(tmp_path: Path) -> None:
    measured = measure_dataset(tmp_path, score_fn=hang_score, timeout=0.5)
    assert measured["value"] is None
    assert measured["seconds"] >= 0.5


def test_run_prints_null_for_timed_out_score(tmp_path: Path, capsys) -> None:
    root = tmp_path / "repo"
    dataset = root / "datasets" / "ds_one"
    dataset.mkdir(parents=True)
    (dataset / "a.txt").write_text("a")
    experiment = Experiment(
        id="ex1",
        type="score_per_measure",
        title="Viewer title",
        datasets=("ds_one",),
        tools=("hang-measure",),
    )
    run_score_per_measure(
        experiment,
        root,
        score_fns={"hang-measure": hang_score},
        timeout=0.5,
        output_dir=tmp_path / "output",
    )
    out = capsys.readouterr().out
    assert "null" in out


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
        id="ex1",
        type="score_per_measure",
        title="Viewer title",
        datasets=("ds_one", "ds_two"),
        tools=("fake-measure", "other-measure"),
    )
    ticks = iter(range(20))
    result = run_score_per_measure(
        experiment,
        root,
        score_fns={
            "fake-measure": lambda path: 0.1 if path.name == "ds_one" else 0.2,
            "other-measure": lambda path: 0.3 if path.name == "ds_one" else 0.4,
        },
        monotonic=lambda: next(ticks),
        output_dir=output_dir,
        workers=1,
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
    png = output_dir / "ex1.png"
    assert png.is_file()
    assert png.stat().st_size > 0
    assert (
        ElementTree.parse(output_dir / "ex1.svg").getroot().tag
        == "{http://www.w3.org/2000/svg}svg"
    )
    out = capsys.readouterr().out
    assert "Scores" in out
    assert "Evaluation time (seconds)" in out
    assert "ds_one" in out and "ds_two" in out
    assert "fake-measure" in out and "other-measure" in out


def test_svg_save_failure_closes_figure(tmp_path: Path, monkeypatch) -> None:
    import matplotlib.pyplot as plt
    from matplotlib.figure import Figure

    dataset = tmp_path / "datasets" / "ds_one"
    dataset.mkdir(parents=True)
    (dataset / "a.txt").write_text("a")
    experiment = Experiment(
        "ex1", "score_per_measure", "Title", ("ds_one",), ("fake-measure",)
    )
    savefig = Figure.savefig
    figures = []

    def fail_svg(fig, path, **kwargs):
        figures.append(fig)
        if Path(path).suffix == ".svg":
            raise OSError("SVG save failed")
        return savefig(fig, path, **kwargs)

    monkeypatch.setattr(Figure, "savefig", fail_svg)
    with pytest.raises(OSError, match="SVG save failed"):
        run_score_per_measure(
            experiment,
            tmp_path,
            score_fns={"fake-measure": lambda _: 0.4},
            output_dir=tmp_path / "output",
        )
    assert len(figures) == 2
    assert figures[0] is figures[1]
    assert not plt.fignum_exists(figures[0].number)


def test_run_prints_job_size_and_per_cell_timing(tmp_path: Path, capsys) -> None:
    root = tmp_path / "repo"
    dataset = root / "datasets" / "ds_one"
    dataset.mkdir(parents=True)
    (dataset / "a.txt").write_text("a")
    experiment = Experiment(
        id="ex1",
        type="score_per_measure",
        title="Viewer title",
        datasets=("ds_one",),
        tools=("fake-measure",),
    )
    run_score_per_measure(
        experiment,
        root,
        score_fns={"fake-measure": lambda path: 0.4},
        output_dir=tmp_path / "output",
    )
    out = capsys.readouterr().out
    assert "ex1: 1 datasets × 1 measures = 1 scores (2 in parallel)" in out
    assert "[1/1] ds_one  fake-measure" in out
    assert "s" in out


def test_run_two_scores_overlap(tmp_path: Path) -> None:
    root = tmp_path / "repo"
    first = root / "datasets" / "ds_one"
    second = root / "datasets" / "ds_two"
    first.mkdir(parents=True)
    second.mkdir(parents=True)
    (first / "a.txt").write_text("a")
    (second / "a.txt").write_text("aa")
    experiment = Experiment(
        id="ex1",
        type="score_per_measure",
        title="Viewer title",
        datasets=("ds_one", "ds_two"),
        tools=("hang-measure",),
    )
    t0 = time.monotonic()
    run_score_per_measure(
        experiment,
        root,
        score_fns={"hang-measure": hang_score},
        timeout=0.5,
        output_dir=tmp_path / "output",
    )
    elapsed = time.monotonic() - t0
    assert elapsed >= 0.5
    assert elapsed < 0.95


def test_plot_panels_use_title_folder_names_and_unit_ylim(tmp_path: Path) -> None:
    import matplotlib

    matplotlib.use("Agg")
    import matplotlib.pyplot as plt

    experiment = Experiment(
        id="ex1",
        type="score_per_measure",
        title="Viewer title",
        datasets=("ds_one", "ds_two"),
        tools=("fake-measure", "other-measure"),
    )
    results = {
        "ds_one": {
            "fake-measure": {"value": 0.25, "seconds": 1.0},
            "other-measure": {"value": 0.40, "seconds": 1.0},
        },
        "ds_two": {
            "fake-measure": {"value": 0.35, "seconds": 1.0},
            "other-measure": {"value": 0.50, "seconds": 1.0},
        },
    }
    fig = plot_scores(results, experiment)
    try:
        assert fig._suptitle.get_text() == "Viewer title"
        assert len(fig.axes) == 2
        for ax, tool, expected in zip(
            fig.axes,
            ("fake-measure", "other-measure"),
            ([0.25, 0.35], [0.40, 0.50]),
        ):
            assert ax.get_title() == tool
            assert ax.get_xlabel() == "Dataset"
            assert ax.get_ylabel() == "Score"
            assert ax.get_ylim() == (0.0, 1.18)
            assert [tick.get_text() for tick in ax.get_xticklabels()] == [
                "ds_one",
                "ds_two",
            ]
            assert ax.collections[0].get_offsets().tolist() == [
                [0.0, expected[0]],
                [1.0, expected[1]],
            ]
            assert [text.get_text() for text in ax.texts] == [
                f"{value:.6f}" for value in expected
            ]
        assert tuple(fig.get_size_inches()) == (10.0, 5.0)
    finally:
        plt.close(fig)


def test_plot_grows_with_dataset_count() -> None:
    import matplotlib

    matplotlib.use("Agg")
    import matplotlib.pyplot as plt

    datasets = tuple(f"ds_{i:02d}" for i in range(15))
    tools = ("fake-measure", "other-measure", "third-measure", "fourth-measure")
    experiment = Experiment(
        id="ex1",
        type="score_per_measure",
        title="Viewer title",
        datasets=datasets,
        tools=tools,
    )
    results = {
        name: {tool: {"value": 0.1, "seconds": 1.0} for tool in tools}
        for name in datasets
    }
    fig = plot_scores(results, experiment)
    try:
        assert tuple(fig.get_size_inches()) == (54.0, 6.3)
    finally:
        plt.close(fig)


def test_plot_annotates_null_and_skips_timed_out_point() -> None:
    import matplotlib

    matplotlib.use("Agg")
    import matplotlib.pyplot as plt

    experiment = Experiment(
        id="ex1",
        type="score_per_measure",
        title="Viewer title",
        datasets=("ds_one", "ds_two"),
        tools=("fake-measure",),
    )
    results = {
        "ds_one": {"fake-measure": {"value": 0.25, "seconds": 1.0}},
        "ds_two": {"fake-measure": {"value": None, "seconds": 1200.0}},
    }
    fig = plot_scores(results, experiment)
    try:
        ax = fig.axes[0]
        assert ax.collections[0].get_offsets().tolist() == [[0.0, 0.25]]
        assert "null" in [text.get_text() for text in ax.texts]
        assert "0.250000" in [text.get_text() for text in ax.texts]
    finally:
        plt.close(fig)
