from pathlib import Path
from random import Random

from experiment_runner.config import Experiment
from experiment_runner.score_for_random_filter import (
    MAX_TRIES,
    MIN_KEEP,
    RELATIVE_EPS,
    SEED,
    run_score_for_random_filter,
)
from experiment_runner.timeout import hang_filter, hang_score, quick_score
from random_filter import SubsetResult, SubsetStep


def _write_dataset(root: Path, name: str, n: int = 8) -> Path:
    path = root / "datasets" / name
    path.mkdir(parents=True)
    for i in range(n):
        (path / f"{i:02d}.txt").write_text(f"{name}-{i}")
    return path


def _experiment(*datasets: str, tools: tuple[str, ...] = ("fake-measure", "other-measure")):
    return Experiment(
        id="rand",
        type="score_for_random_filter",
        title="Viewer title",
        datasets=datasets,
        tools=tools,
    )


def _steps_for(paths: list[Path]) -> list[SubsetStep]:
    half = paths[: max(1, len(paths) // 2)]
    n = len(paths)
    return [
        SubsetStep(0, 0.6, n, 100.0, tuple(paths)),
        SubsetStep(1, 0.7, len(half), 100.0 * len(half) / n, tuple(half)),
    ]


def fake_filter(paths, measure, *, relative_eps, max_tries, min_keep, rng):
    paths = list(paths)
    steps = _steps_for(paths)
    return SubsetResult(kept=list(steps[-1].remaining), steps=steps)


def test_constants() -> None:
    assert SEED == 0
    assert RELATIVE_EPS == 1e-5
    assert MAX_TRIES == 10
    assert MIN_KEEP == 10


def test_filter_once_per_dataset_with_first_tool_and_knobs(tmp_path: Path) -> None:
    root = tmp_path / "repo"
    _write_dataset(root, "ds_one")
    _write_dataset(root, "ds_two")
    calls: list[dict] = []
    filter_measure_calls: list[Path] = []

    def filter_measure(path: Path) -> float:
        filter_measure_calls.append(path)
        return 0.2

    def extra_measure(_path: Path) -> float:
        return 0.3

    def recording_filter(paths, measure, *, relative_eps, max_tries, min_keep, rng):
        calls.append(
            {
                "names": [p.name for p in paths],
                "measure": measure,
                "relative_eps": relative_eps,
                "max_tries": max_tries,
                "min_keep": min_keep,
                "rng_first": rng.randrange(2**32),
            }
        )
        return fake_filter(
            paths,
            measure,
            relative_eps=relative_eps,
            max_tries=max_tries,
            min_keep=min_keep,
            rng=rng,
        )

    run_score_for_random_filter(
        _experiment("ds_one", "ds_two"),
        root,
        score_fns={"fake-measure": filter_measure, "other-measure": extra_measure},
        filter_fn=recording_filter,
        output_dir=tmp_path / "output",
    )
    assert len(calls) == 2
    expected_rng = Random(0).randrange(2**32)
    for call in calls:
        assert call["names"] == [f"{i:02d}.txt" for i in range(8)]
        assert call["measure"] is filter_measure
        assert call["relative_eps"] == 1e-5
        assert call["max_tries"] == 10
        assert call["min_keep"] == 10
        assert call["rng_first"] == expected_rng
    assert filter_measure_calls == []


def test_extra_tool_scores_each_remaining_set(tmp_path: Path) -> None:
    root = tmp_path / "repo"
    files_dir = _write_dataset(root, "ds_one")
    seen: list[list[str]] = []

    def extra_measure(path: Path) -> float:
        seen.append(sorted(p.name for p in path.iterdir() if p.is_file()))
        return 0.4

    result = run_score_for_random_filter(
        _experiment("ds_one"),
        root,
        score_fns={
            "fake-measure": lambda _p: 0.2,
            "other-measure": extra_measure,
        },
        filter_fn=fake_filter,
        output_dir=tmp_path / "output",
    )
    names = sorted(p.name for p in files_dir.iterdir() if p.is_file())
    half = names[:4]
    assert seen == [names, half]
    steps = result["ds_one"]["steps"]
    assert steps[0]["measures"]["fake-measure"] == {"value": 0.6, "seconds": None}
    assert steps[1]["measures"]["fake-measure"] == {"value": 0.7, "seconds": None}
    assert steps[0]["measures"]["other-measure"]["value"] == 0.4
    assert steps[1]["measures"]["other-measure"]["value"] == 0.4
    assert steps[0]["remaining_count"] == 8
    assert steps[1]["remaining_count"] == 4
    png = tmp_path / "output" / "rand.png"
    assert png.is_file()
    assert png.stat().st_size > 0


def test_one_tool_skips_extra_scoring(tmp_path: Path) -> None:
    root = tmp_path / "repo"
    _write_dataset(root, "ds_one")
    extra_calls: list[Path] = []

    def extra_measure(path: Path) -> float:
        extra_calls.append(path)
        return 0.4

    result = run_score_for_random_filter(
        _experiment("ds_one", tools=("fake-measure",)),
        root,
        score_fns={"fake-measure": extra_measure},
        filter_fn=fake_filter,
        output_dir=tmp_path / "output",
    )
    assert extra_calls == []
    assert result["ds_one"]["steps"][0]["measures"]["fake-measure"]["value"] == 0.6
    assert (tmp_path / "output" / "rand.png").is_file()


def test_filter_timeout_skips_extra_scores(tmp_path: Path, capsys) -> None:
    root = tmp_path / "repo"
    _write_dataset(root, "ds_one")
    extra_calls: list[Path] = []

    def extra_measure(path: Path) -> float:
        extra_calls.append(path)
        return 0.4

    result = run_score_for_random_filter(
        _experiment("ds_one"),
        root,
        score_fns={"fake-measure": quick_score, "other-measure": extra_measure},
        filter_fn=hang_filter,
        timeout=0.5,
        output_dir=tmp_path / "output",
    )
    assert result["ds_one"]["steps"] is None
    assert extra_calls == []
    assert (tmp_path / "output" / "rand.png").is_file()
    assert "kept=null" in capsys.readouterr().out


def test_empty_steps_skip_extra_scores(tmp_path: Path) -> None:
    root = tmp_path / "repo"
    _write_dataset(root, "ds_one")
    extra_calls: list[Path] = []

    def extra_measure(path: Path) -> float:
        extra_calls.append(path)
        return 0.4

    def empty_filter(paths, measure, *, relative_eps, max_tries, min_keep, rng):
        return SubsetResult(kept=list(paths), steps=[])

    result = run_score_for_random_filter(
        _experiment("ds_one"),
        root,
        score_fns={
            "fake-measure": lambda _p: 0.2,
            "other-measure": extra_measure,
        },
        filter_fn=empty_filter,
        output_dir=tmp_path / "output",
    )
    assert result["ds_one"]["steps"] == []
    assert extra_calls == []
    assert (tmp_path / "output" / "rand.png").is_file()


def test_extra_measure_timeout_is_null(tmp_path: Path) -> None:
    root = tmp_path / "repo"
    _write_dataset(root, "ds_one")
    result = run_score_for_random_filter(
        _experiment("ds_one", tools=("fake-measure", "hang-measure")),
        root,
        score_fns={"fake-measure": lambda _p: 0.2, "hang-measure": hang_score},
        filter_fn=fake_filter,
        timeout=0.5,
        output_dir=tmp_path / "output",
    )
    steps = result["ds_one"]["steps"]
    assert steps[0]["measures"]["fake-measure"]["value"] == 0.6
    assert steps[0]["measures"]["hang-measure"]["value"] is None
    assert steps[1]["measures"]["hang-measure"]["value"] is None


def test_progress_prints_dataset_and_steps(tmp_path: Path, capsys) -> None:
    root = tmp_path / "repo"
    _write_dataset(root, "ds_one")
    run_score_for_random_filter(
        _experiment("ds_one"),
        root,
        score_fns={
            "fake-measure": lambda _p: 0.2,
            "other-measure": lambda _p: 0.3,
        },
        filter_fn=fake_filter,
        output_dir=tmp_path / "output",
    )
    out = capsys.readouterr().out
    assert "ds_one fake-measure" in out
    assert "ds_one step=0 kept=8 fake-measure=0.600000 other-measure=0.300000" in out
    assert "ds_one step=1 kept=4 fake-measure=0.700000 other-measure=0.300000" in out


def test_plot_steps_grid_titles_ylim_labels_and_nan() -> None:
    import math

    import matplotlib

    matplotlib.use("Agg")
    import matplotlib.pyplot as plt

    from experiment_runner.score_for_random_filter import plot_steps_grid

    experiment = _experiment("ds_one", "ds_two")

    def _dataset(filter_value: float, extra_none_at: int | None = 1):
        return {
            "filter_seconds": 1.0,
            "steps": [
                {
                    "index": 0,
                    "remaining_count": 8,
                    "remaining_pct": 100.0,
                    "measures": {
                        "fake-measure": {"value": filter_value, "seconds": None},
                        "other-measure": {"value": 0.4, "seconds": 0.1},
                    },
                },
                {
                    "index": 1,
                    "remaining_count": 4,
                    "remaining_pct": 50.0,
                    "measures": {
                        "fake-measure": {"value": filter_value + 0.1, "seconds": None},
                        "other-measure": {
                            "value": None if extra_none_at == 1 else 0.5,
                            "seconds": 0.1,
                        },
                    },
                },
            ],
        }

    results = {
        "ds_one": _dataset(0.2),
        "ds_two": {"filter_seconds": 0.0, "steps": None},
    }
    fig = plot_steps_grid(results, experiment)
    try:
        assert fig._suptitle.get_text() == "Viewer title"
        assert len(fig.axes) == 2
        assert [ax.get_title() for ax in fig.axes] == [
            "ds_one — random-filter",
            "ds_two — random-filter",
        ]
        ax = fig.axes[0]
        assert ax.get_ylim() == (0.0, 1.0)
        assert ax.get_xlabel() == "step"
        assert ax.get_ylabel() == "Score"
        assert len(ax.get_lines()) == 2
        extra = ax.get_lines()[1]
        ys = list(extra.get_ydata())
        assert math.isnan(float(ys[1]))
        texts = [text.get_text() for text in ax.texts]
        assert len(texts) == 2
        assert "100.0%" in texts[0] and "8" in texts[0]
        assert "50.0%" in texts[1] and "4" in texts[1]
        assert fig.axes[1].get_lines() == []
    finally:
        plt.close(fig)
