from pathlib import Path
from xml.etree import ElementTree
from random import Random

from experiment_runner.config import Experiment
from experiment_runner.score_for_random_filter import (
    MAX_TRIES,
    RELATIVE_EPS,
    RUN_COUNT,
    SEEDS,
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


def fake_filter(paths, measure, *, relative_eps, max_tries, rng):
    paths = list(paths)
    steps = _steps_for(paths)
    return SubsetResult(kept=list(steps[-1].remaining), steps=steps)


def test_constants() -> None:
    assert RUN_COUNT == 10
    assert SEEDS == tuple(range(10))
    assert RELATIVE_EPS == 1e-5
    assert MAX_TRIES == 10


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

    def recording_filter(paths, measure, *, relative_eps, max_tries, rng):
        calls.append(
            {
                "names": [p.name for p in paths],
                "measure": measure,
                "relative_eps": relative_eps,
                "max_tries": max_tries,
                "rng_first": rng.randrange(2**32),
            }
        )
        return fake_filter(
            paths,
            measure,
            relative_eps=relative_eps,
            max_tries=max_tries,
            rng=rng,
        )

    result = run_score_for_random_filter(
        _experiment("ds_one", "ds_two"),
        root,
        score_fns={"fake-measure": filter_measure, "other-measure": extra_measure},
        filter_fn=recording_filter,
        output_dir=tmp_path / "output",
    )
    assert len(calls) == 20
    expected_rng = [Random(seed).randrange(2**32) for seed in SEEDS]
    for i, call in enumerate(calls):
        seed = i % 10
        assert call["names"] == [f"{j:02d}.txt" for j in range(8)]
        assert call["measure"] is filter_measure
        assert call["relative_eps"] == 1e-5
        assert call["max_tries"] == 10
        assert "min_keep" not in call
        assert call["rng_first"] == expected_rng[seed]
    assert filter_measure_calls == []
    assert len(result["ds_one"]["runs"]) == 10
    assert len(result["ds_two"]["runs"]) == 10


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
    assert seen == [names, half] * 10
    steps = result["ds_one"]["runs"][0]["steps"]
    assert steps[0]["measures"]["fake-measure"] == {"value": 0.6, "seconds": None}
    assert steps[1]["measures"]["fake-measure"] == {"value": 0.7, "seconds": None}
    assert steps[0]["measures"]["other-measure"]["value"] == 0.4
    assert steps[1]["measures"]["other-measure"]["value"] == 0.4
    assert steps[0]["remaining_count"] == 8
    assert steps[1]["remaining_count"] == 4
    png = tmp_path / "output" / "rand.png"
    assert png.is_file()
    assert png.stat().st_size > 0
    assert (
        ElementTree.parse(png.with_suffix(".svg")).getroot().tag
        == "{http://www.w3.org/2000/svg}svg"
    )


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
    assert result["ds_one"]["runs"][0]["steps"][0]["measures"]["fake-measure"]["value"] == 0.6
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
    assert all(run["steps"] is None for run in result["ds_one"]["runs"])
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

    def empty_filter(paths, measure, *, relative_eps, max_tries, rng):
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
    assert result["ds_one"]["runs"][0]["steps"] == []
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
    steps = result["ds_one"]["runs"][0]["steps"]
    assert steps[0]["measures"]["fake-measure"]["value"] == 0.6
    assert steps[0]["measures"]["hang-measure"]["value"] is None
    assert steps[1]["measures"]["hang-measure"]["value"] is None


def test_one_timed_out_run_keeps_the_others(tmp_path: Path):
    root = tmp_path / "repo"
    _write_dataset(root, "ds_one")
    calls = {"n": 0}

    def first_hangs(paths, measure, *, relative_eps, max_tries, rng):
        calls["n"] += 1
        if calls["n"] == 1:
            # Nested filters run in-process (unpicklable); hang_filter would
            # sleep past timeout. Returning None is what call_timed yields.
            return None
        return fake_filter(
            paths, measure, relative_eps=relative_eps, max_tries=max_tries, rng=rng
        )

    result = run_score_for_random_filter(
        _experiment("ds_one"),
        root,
        score_fns={"fake-measure": lambda _p: 0.2, "other-measure": lambda _p: 0.3},
        filter_fn=first_hangs,
        timeout=0.5,
        output_dir=tmp_path / "output",
    )
    runs = result["ds_one"]["runs"]
    assert [run["seed"] for run in runs] == list(range(10))
    assert runs[0]["steps"] is None
    assert all(run["steps"] for run in runs[1:])


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
    assert "ds_one run=0 fake-measure" in out
    assert "ds_one run=0 step=0 kept=8 fake-measure=0.600000 other-measure=0.300000" in out
    assert "ds_one run=0 step=1 kept=4 fake-measure=0.700000 other-measure=0.300000" in out
    assert "ds_one run=9 step=1 kept=4 fake-measure=0.700000 other-measure=0.300000" in out


def test_plot_exact_landing_ladder_and_counts():
    import matplotlib

    matplotlib.use("Agg")
    import matplotlib.pyplot as plt

    from experiment_runner.score_for_random_filter import plot_steps_grid

    experiment = _experiment("ds_one", tools=("fake-measure",))

    def _step(index: int, remaining_count: int, remaining_pct: float, value: float):
        return {
            "index": index,
            "remaining_count": remaining_count,
            "remaining_pct": remaining_pct,
            "measures": {"fake-measure": {"value": value, "seconds": None}},
        }

    results = {
        "ds_one": {
            "runs": [
                {
                    "seed": 0,
                    "filter_seconds": 1.0,
                    "steps": [
                        _step(0, 100, 100.0, 0.10),
                        _step(1, 50, 50.0, 0.20),
                        _step(2, 25, 25.0, 0.30),
                        _step(3, 14, 14.0, 0.70),
                    ],
                },
                {
                    "seed": 1,
                    "filter_seconds": 1.0,
                    "steps": [
                        _step(0, 100, 100.0, 0.15),
                        _step(1, 50, 50.0, 0.25),
                        _step(2, 25, 25.0, 0.50),
                        _step(3, 12, 12.0, 0.80),
                    ],
                },
            ],
        },
    }
    fig = plot_steps_grid(results, experiment)
    try:
        ax = fig.axes[0]
        assert ax.get_xlabel() == "remaining %"
        assert not any(list(line.get_xdata()) == [0, 1, 2, 3] for line in ax.get_lines())
        labels = [tick.get_text() for tick in ax.get_xticklabels()]
        assert labels == [
            "100.0%\n100\nn=2",
            "50.0%\n50\nn=2",
            "25.0%\n25\nn=2",
            "14.0%\n14\nn=1",
            "12.0%\n12\nn=1",
        ]
        boxes = list(ax.patches)
        assert len(boxes) == 5

        def _y_span(patch):
            ys = [vertex[1] for vertex in patch.get_path().vertices]
            return min(ys), max(ys)

        low25, high25 = _y_span(boxes[2])
        assert high25 - low25 > 0
        low14, high14 = _y_span(boxes[3])
        assert high14 - low14 == 0
        assert low14 == 0.70
    finally:
        plt.close(fig)


def test_plot_steps_grid_titles_ylim_labels_and_nan() -> None:
    import matplotlib

    matplotlib.use("Agg")
    import matplotlib.pyplot as plt

    from experiment_runner.score_for_random_filter import plot_steps_grid

    experiment = _experiment("ds_one", "ds_two")

    def _dataset(filter_value: float, extra_none_at: int | None = 1):
        return {
            "runs": [
                {
                    "seed": 0,
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
            ],
        }

    results = {
        "ds_one": _dataset(0.2),
        "ds_two": {
            "runs": [{"seed": 0, "filter_seconds": 0.0, "steps": None}],
        },
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
        assert ax.get_xlabel() == "remaining %"
        assert ax.get_ylabel() == "Score"
        labels = [tick.get_text() for tick in ax.get_xticklabels()]
        assert labels == [
            "100.0%\n8\nn=1",
            "50.0%\n4\nn=1",
        ]
        assert len(ax.patches) == 3
        assert list(fig.axes[1].patches) == []
    finally:
        plt.close(fig)


def test_plot_steps_grid_uses_pinned_measure_colors() -> None:
    import matplotlib

    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    from matplotlib.colors import to_rgba

    from experiment_runner.score_for_random_filter import plot_steps_grid

    experiment = Experiment(
        id="rand",
        type="score_for_random_filter",
        title="Viewer title",
        datasets=("ds_one",),
        tools=("levassor-measure", "panhard-measure"),
    )
    results = {
        "ds_one": {
            "runs": [
                {
                    "seed": 0,
                    "filter_seconds": 1.0,
                    "steps": [
                        {
                            "index": 0,
                            "remaining_count": 8,
                            "remaining_pct": 100.0,
                            "measures": {
                                "levassor-measure": {"value": 0.2, "seconds": None},
                                "panhard-measure": {"value": 0.4, "seconds": 0.1},
                            },
                        },
                    ],
                }
            ],
        },
    }
    fig = plot_steps_grid(results, experiment)
    try:
        boxes = fig.axes[0].patches
        assert to_rgba(boxes[0].get_facecolor()) == to_rgba("C1")
        assert to_rgba(boxes[1].get_facecolor()) == to_rgba("C0")
    finally:
        plt.close(fig)
