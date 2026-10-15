from pathlib import Path

from experiment_runner.config import Experiment
from experiment_runner.score_per_measure import (
    measure_dataset,
    plot_scores,
    run_score_per_measure,
)


def test_measure_dataset_times_injected_score(tmp_path: Path) -> None:
    ticks = iter([10.0, 10.25])
    measured = measure_dataset(
        tmp_path, score_fn=lambda path: 0.4, monotonic=lambda: next(ticks)
    )
    assert measured == {"value": 0.4, "seconds": 0.25}


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
        tools=("fake-metric", "other-metric"),
    )
    ticks = iter(range(20))
    result = run_score_per_measure(
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
    png = output_dir / "ex1.png"
    assert png.is_file()
    assert png.stat().st_size > 0
    assert not (output_dir / "ex1.svg").exists()
    out = capsys.readouterr().out
    assert "Scores" in out
    assert "Evaluation time (seconds)" in out
    assert "ds_one" in out and "ds_two" in out
    assert "fake-metric" in out and "other-metric" in out


def test_plot_panels_use_title_folder_names_and_unit_ylim(tmp_path: Path) -> None:
    import matplotlib

    matplotlib.use("Agg")
    import matplotlib.pyplot as plt

    experiment = Experiment(
        id="ex1",
        type="score_per_measure",
        title="Viewer title",
        datasets=("ds_one", "ds_two"),
        tools=("fake-metric", "other-metric"),
    )
    results = {
        "ds_one": {
            "fake-metric": {"value": 0.25, "seconds": 1.0},
            "other-metric": {"value": 0.40, "seconds": 1.0},
        },
        "ds_two": {
            "fake-metric": {"value": 0.35, "seconds": 1.0},
            "other-metric": {"value": 0.50, "seconds": 1.0},
        },
    }
    fig = plot_scores(results, experiment)
    try:
        assert fig._suptitle.get_text() == "Viewer title"
        assert len(fig.axes) == 2
        for ax, tool, expected in zip(
            fig.axes,
            ("fake-metric", "other-metric"),
            ([0.25, 0.35], [0.40, 0.50]),
        ):
            assert ax.get_title() == tool
            assert ax.get_xlabel() == "Dataset"
            assert ax.get_ylabel() == "Score"
            assert ax.get_ylim() == (0.0, 1.0)
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
    finally:
        plt.close(fig)
