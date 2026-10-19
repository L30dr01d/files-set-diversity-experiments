from pathlib import Path

from experiment_runner.config import Experiment
from experiment_runner.score_for_fastr import (
    BUDGET_PCTS,
    FASTR_ALGOS,
    plot_budget_grid,
    run_score_for_fastr,
)
from experiment_runner.timeout import hang_reduce, hang_score


def _write_dataset(root: Path, name: str, n: int = 20) -> Path:
    path = root / "datasets" / name
    path.mkdir(parents=True)
    for i in range(n):
        (path / f"{i:02d}.txt").write_text(f"{name}-{i}")
    return path


def _experiment(*datasets: str) -> Experiment:
    return Experiment(
        id="fastr",
        type="score_for_fastr",
        title="Viewer title",
        datasets=datasets,
        tools=("fake-measure", "other-measure"),
    )


def fake_reduce(files_dir: Path, algo: str, pct: float) -> list[str]:
    names = sorted(p.name for p in files_dir.iterdir() if p.is_file())
    n = max(1, int(len(names) * pct / 100))
    return names[:n]


def test_constants() -> None:
    assert FASTR_ALGOS == ("FAST++", "FAST-CS")
    assert BUDGET_PCTS == tuple(range(100, 0, -5))
    assert BUDGET_PCTS[0] == 100
    assert BUDGET_PCTS[-1] == 5


def test_one_hundred_percent_skips_reduce(tmp_path: Path) -> None:
    root = tmp_path / "repo"
    _write_dataset(root, "ds_one")
    calls: list[tuple] = []

    def counting_reduce(files_dir, algo, pct):
        calls.append((files_dir.name, algo, pct))
        return fake_reduce(files_dir, algo, pct)

    run_score_for_fastr(
        _experiment("ds_one"),
        root,
        score_fns={
            "fake-measure": lambda path: 0.2,
            "other-measure": lambda path: 0.3,
        },
        reduce_fn=counting_reduce,
        output_dir=tmp_path / "output",
    )
    assert all(pct != 100 for (_name, _algo, pct) in calls)


def test_reduce_once_per_dataset_algo_percent(tmp_path: Path) -> None:
    root = tmp_path / "repo"
    _write_dataset(root, "ds_one")
    _write_dataset(root, "ds_two")
    calls: list[tuple] = []

    def counting_reduce(files_dir, algo, pct):
        calls.append((files_dir.name, algo, float(pct)))
        return fake_reduce(files_dir, algo, pct)

    run_score_for_fastr(
        _experiment("ds_one", "ds_two"),
        root,
        score_fns={
            "fake-measure": lambda path: 0.2,
            "other-measure": lambda path: 0.3,
        },
        reduce_fn=counting_reduce,
        output_dir=tmp_path / "output",
    )
    expected = [
        (name, algo, float(pct))
        for name in ("ds_one", "ds_two")
        for algo in ("FAST++", "FAST-CS")
        for pct in range(95, 0, -5)
    ]
    assert calls == expected


def test_run_writes_png_and_scores_one_hundred(tmp_path: Path) -> None:
    root = tmp_path / "repo"
    _write_dataset(root, "ds_one")
    result = run_score_for_fastr(
        _experiment("ds_one"),
        root,
        score_fns={
            "fake-measure": lambda path: 0.4,
            "other-measure": lambda path: 0.5,
        },
        reduce_fn=fake_reduce,
        output_dir=tmp_path / "output",
    )
    png = tmp_path / "output" / "fastr.png"
    assert png.is_file()
    assert png.stat().st_size > 0
    entry = result["ds_one"]["FAST++"][100]
    assert entry["kept_count"] == 20
    assert entry["reduce_seconds"] is None
    assert entry["measures"]["fake-measure"]["value"] == 0.4
    assert entry["measures"]["other-measure"]["value"] == 0.5


def test_reduce_timeout_skips_score(tmp_path: Path) -> None:
    root = tmp_path / "repo"
    _write_dataset(root, "ds_one", n=4)
    score_calls: list[Path] = []

    def counting_score(path: Path) -> float:
        score_calls.append(path)
        return 0.5

    result = run_score_for_fastr(
        Experiment(
            id="fastr",
            type="score_for_fastr",
            title="Viewer title",
            datasets=("ds_one",),
            tools=("fake-measure",),
        ),
        root,
        score_fns={"fake-measure": counting_score},
        reduce_fn=hang_reduce,
        timeout=0.5,
        output_dir=tmp_path / "output",
    )
    timed = result["ds_one"]["FAST++"][95]
    assert timed["kept_count"] is None
    assert timed["measures"]["fake-measure"]["value"] is None
    # 100% still scores the source dir once per algo
    assert len(score_calls) == 2


def test_plot_grid_titles_ylim_and_nan_break() -> None:
    import math

    import matplotlib

    matplotlib.use("Agg")
    import matplotlib.pyplot as plt

    experiment = _experiment("ds_one", "ds_two")
    def _budget(value):
        return {
            pct: {
                "kept_count": 1,
                "reduce_seconds": None,
                "measures": {
                    "fake-measure": {"value": value, "seconds": 0.0},
                    "other-measure": {"value": None if pct == 50 else value, "seconds": 0.0},
                },
            }
            for pct in BUDGET_PCTS
        }

    results = {
        "ds_one": {"FAST++": _budget(0.2), "FAST-CS": _budget(0.3)},
        "ds_two": {"FAST++": _budget(0.4), "FAST-CS": _budget(0.5)},
    }
    fig = plot_budget_grid(results, experiment)
    try:
        assert fig._suptitle.get_text() == "Viewer title"
        assert len(fig.axes) == 4
        titles = [ax.get_title() for ax in fig.axes]
        assert titles == [
            "ds_one — FAST++",
            "ds_one — FAST-CS",
            "ds_two — FAST++",
            "ds_two — FAST-CS",
        ]
        ax = fig.axes[0]
        assert ax.get_ylim() == (0.0, 1.0)
        assert ax.get_xlabel() == "budget % of original suite"
        assert ax.get_ylabel() == "Score"
        labels = [tick.get_text() for tick in ax.get_xticklabels()]
        assert "100" in labels and "5" in labels
        assert len(ax.get_lines()) == 2
        other = ax.get_lines()[1]
        ys = list(other.get_ydata())
        fifty_index = list(BUDGET_PCTS).index(50)
        assert math.isnan(float(ys[fifty_index]))
    finally:
        plt.close(fig)


def test_plot_budget_grid_uses_pinned_measure_colors() -> None:
    import matplotlib

    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    from matplotlib.colors import to_rgba

    experiment = Experiment(
        id="fastr",
        type="score_for_fastr",
        title="Viewer title",
        datasets=("ds_one",),
        tools=("levassor-measure", "panhard-v3-measure"),
    )
    cell = {
        pct: {
            "kept_count": 1,
            "reduce_seconds": None,
            "measures": {
                "levassor-measure": {"value": 0.2, "seconds": 0.0},
                "panhard-v3-measure": {"value": 0.3, "seconds": 0.0},
            },
        }
        for pct in BUDGET_PCTS
    }
    results = {"ds_one": {"FAST++": cell, "FAST-CS": cell}}
    fig = plot_budget_grid(results, experiment)
    try:
        lines = fig.axes[0].get_lines()
        assert to_rgba(lines[0].get_color()) == to_rgba("C1")
        assert to_rgba(lines[1].get_color()) == to_rgba("C0")
    finally:
        plt.close(fig)


def test_score_timeout_is_null(tmp_path: Path) -> None:
    root = tmp_path / "repo"
    _write_dataset(root, "ds_one", n=4)
    result = run_score_for_fastr(
        Experiment(
            id="fastr",
            type="score_for_fastr",
            title="t",
            datasets=("ds_one",),
            tools=("hang-measure",),
        ),
        root,
        score_fns={"hang-measure": hang_score},
        reduce_fn=fake_reduce,
        timeout=0.5,
        output_dir=tmp_path / "output",
    )
    assert result["ds_one"]["FAST++"][100]["measures"]["hang-measure"]["value"] is None
