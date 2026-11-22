from pathlib import Path

from experiment_runner.analyzer_coverage import ImageCoverage
from experiment_runner.config import Experiment
from panhard_filter import FilterResult
from panhard_filter.filter import FilterStep


def test_profiles_each_exact_subset_for_both_analyzers(tmp_path, monkeypatch):
    from experiment_runner import coverage_with_filter_panhard as module

    datasets = ("larger", "smaller", "timeout")
    experiment = Experiment("sweep", "coverage_with_filter_panhard_rni", "Sweep", datasets, ())
    for dataset, size in zip(datasets, (4, 3, 2)):
        directory = tmp_path / "datasets" / dataset
        directory.mkdir(parents=True)
        for i in range(size):
            (directory / f"{i}.sv").touch()

    expected = []

    def filter_trace(paths, ranking, **kwargs):
        assert ranking == "rni"
        if paths[0].parent.name == "timeout":
            return None
        steps = [
            FilterStep(count, float(count), tuple(paths[:count]), 0.25)
            for count in range(len(paths), 1, -1)
        ]
        expected.extend(
            (tool, step.remaining)
            for step in steps
            for tool in ("iverilog", "verilator")
        )
        return FilterResult(list(steps[-1].remaining), steps, 2)

    calls = []
    directories = set()

    def profile(analyzer, sources, profile_dir, timeout):
        calls.append((analyzer, tuple(sources)))
        assert profile_dir not in directories
        directories.add(profile_dir)
        points = frozenset(path.name for path in sources)
        if analyzer == "verilator":
            points = frozenset({"verilator-only"})
        return ImageCoverage(points, points, frozenset(), frozenset())

    monkeypatch.setattr(module, "timed_panhard_filter", filter_trace)
    output = tmp_path / "output"
    result = module.run_coverage_with_filter_panhard(
        experiment, tmp_path, ranking="rni", output_dir=output, run_set=profile
    )
    assert calls == expected
    assert len(calls) == 10
    assert result["larger"]["steps"][-1]["coverage"]["iverilog"] == {"line": 50, "mcdc": 0}
    assert result["smaller"]["steps"][-1]["coverage"]["iverilog"]["line"] == 200 / 3
    assert result["larger"]["steps"][-1]["coverage"]["verilator"]["line"] == 100
    assert result["timeout"]["steps"] is None
    assert (output / "sweep.png").stat().st_size
    assert (output / "sweep.svg").stat().st_size

    import matplotlib.pyplot as plt

    fig = module.plot_panhard_coverage(result, experiment)
    try:
        assert [axis.get_title() for axis in fig.axes[:3]] == list(datasets)
        assert len(fig.axes) == 9
        assert fig.axes[0].get_shared_x_axes().joined(fig.axes[0], fig.axes[6])
        assert not fig.axes[0].get_shared_x_axes().joined(fig.axes[0], fig.axes[1])
        assert [len(series) for series in fig.axes[3].containers] == [3, 3]
        assert [len(series) for series in fig.axes[7].containers] == [2, 2]
        assert all(axis.lines[-1].get_xdata()[0] == 2 for axis in fig.axes[0::3])
        assert any("timeout" in label.get_text().lower() for label in fig.axes[2].texts)
    finally:
        plt.close(fig)


def test_two_file_dataset_shows_diversity_and_residual():
    import matplotlib.pyplot as plt
    from matplotlib.container import ErrorbarContainer

    from experiment_runner.coverage_with_filter_panhard import plot_panhard_coverage

    experiment = Experiment("two", "coverage_with_filter_panhard_rni", "Two files", ("data",), ())
    step = {
        "remaining_count": 2,
        "score": 3.0,
        "residual": -0.5,
        "coverage": {
            "iverilog": {"line": 50, "mcdc": 25},
            "verilator": {"line": 75, "mcdc": 50},
        },
    }
    fig = plot_panhard_coverage({"data": {"stop_count": 2, "steps": [step]}}, experiment)
    try:
        errorbar, = (
            item for item in fig.axes[0].containers if isinstance(item, ErrorbarContainer)
        )
        marker, _, (interval,) = errorbar.lines
        assert marker.get_marker() == "o"
        assert list(marker.get_ydata()) == [3.0]
        assert interval.get_segments()[0].tolist() == [[2, 2.5], [2, 3.5]]
    finally:
        plt.close(fig)
