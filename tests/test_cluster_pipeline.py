from pathlib import Path
import json

import pytest

from experiment_runner import worker
from experiment_runner.cli import main, matrix_payload
from experiment_runner.config import ConfigError, load_config, parse_config
from experiment_runner.plotly_figures import build_figure
from experiment_runner.results import collect_cells


def ordinary():
    return dict(
        id="demo",
        title="Demo",
        type="score_per_measure",
        runtime_clusters=[
            dict(datasets=["a", "b"], tools=["first-measure"]),
            dict(datasets=["b"], tools=["second-measure"]),
        ],
    )


def test_pilot_and_matrix_bounds():
    experiments = load_config(Path(__file__).resolve().parents[1])
    pilot = next(e for e in experiments if e.id == "16_deptycheck")
    assert len({cell for cluster in pilot.clusters for cell in cluster.cells()}) == 60
    assert len(pilot.datasets) == 30
    assert pilot.tools == ("panhard-measure", "levassor-measure")
    assert (
        sum(
            r.get("experiment_id") == pilot.id
            for r in matrix_payload(experiments)["include"]
        )
        == len(pilot.clusters)
    )


def test_overlap_and_sparse_plan():
    entry = ordinary()
    entry["runtime_clusters"][1]["tools"].append("first-measure")
    with pytest.raises(ConfigError, match="overlapping"):
        parse_config(dict(experiments=[entry]))


def test_split_partial_and_local(tmp_path, monkeypatch):
    config = dict(experiments=[ordinary()])
    (tmp_path / "experiments.json").write_text(json.dumps(config))
    for folder in (
        "datasets/a",
        "datasets/b",
        "tools/first-measure",
        "tools/second-measure",
    ):
        (tmp_path / folder).mkdir(parents=True)
    calls = []

    def measure(exp, dataset, column, root, scratch):
        calls.append((dataset, column))
        if dataset == "b" and column == "first-measure":
            raise TimeoutError()
        return {"value": 0, "seconds": 3, "peak_memory_mib": 1}

    monkeypatch.setattr(worker, "compute_cell", measure)
    results = tmp_path / "results"

    def run(*args):
        assert main(list(map(str, args)), root=tmp_path) == 0

    run("worker", "demo--1", "--results-dir", results)
    exp = load_config(tmp_path)[0]
    cells = collect_cells(exp, results)
    assert cells["b", "second-measure"] is None and cells["b", "first-measure"] is None
    assert ("a", "second-measure") not in cells and cells["a", "first-measure"][
        "value"
    ] == 0
    run("aggregate", "--results-dir", results, "--output-dir", tmp_path / "partial")
    assert (tmp_path / "partial/demo.html").is_file()
    run("worker", "demo--2", "--results-dir", results)
    figure = build_figure(exp, collect_cells(exp, results))
    assert figure.layout.updatemenus[0].buttons[1].args[0]["yaxis.range"] == [0, 1]
    assert [list(t.y) for t in figure.data] == [[0], [None], [0]]
    assert calls == [
        ("a", "first-measure"),
        ("b", "first-measure"),
        ("b", "second-measure"),
    ]
    run("run", "demo")
    assert calls[:3] == calls[3:]
    assert (tmp_path / "output/demo.html").is_file()


@pytest.mark.parametrize(
    "kind",
    [
        "score_for_fastr",
        "score_for_random_filter",
        "score_for_panhard_dpi",
        "coverage_with_filter",
        "coverage_with_filter_panhard_rni",
        "measure_per_set",
    ],
)
def test_all_missing_family(tmp_path, kind):
    entry = ordinary()
    entry["type"] = kind
    entry["runtime_clusters"] = [{"datasets": ["a"]}]
    if kind == "score_for_fastr":
        entry["runtime_clusters"][0]["tools"] = ["FAST++"]
        entry["scorers"] = ["x"]
    elif not kind.startswith("coverage_"):
        entry["runtime_clusters"][0]["tools"] = ["x"]
    exp = parse_config(dict(experiments=[entry]))[0]
    assert build_figure(exp, collect_cells(exp, tmp_path)).layout.title.text.endswith(
        "1 missing executions"
    )


def test_random_distributions_and_subset_alignment():
    e = ordinary()
    e["type"] = "score_for_random_filter"
    exp = parse_config(dict(experiments=[e]))[0]

    def trace(tool, fingerprint):
        step = dict(
            remaining_count=3,
            remaining_pct=75,
            subset_digest=fingerprint,
            measures={"first-measure": {"value": 0.5}, tool: {"value": 0.5}},
        )
        return {"runs": [{"seed": 1, "steps": [step, step]}]}

    cells = {
        ("b", "first-measure"): trace("first-measure", "same"),
        ("b", "second-measure"): trace("second-measure", "same"),
    }
    fig = build_figure(exp, cells)
    assert [t.type for t in fig.data] == ["box", "box"]
    assert list(fig.data[0].y) == [0.5] and "n=1" in fig.data[0].x[0]
    cells["b", "second-measure"] = trace("second-measure", "different")
    with pytest.raises(ValueError, match="trace"):
        build_figure(exp, cells)


def test_panhard_fit_includes_residual():
    entry = ordinary()
    entry["type"] = "score_for_panhard_dpi"
    exp = parse_config(dict(experiments=[entry]))[0]
    step = dict(
        remaining_count=2,
        subset_digest="same",
        measures={
            "panhard-measure": {"value": 0.5, "residual": 0.2},
            "first-measure": {"value": 0.5},
        },
    )
    fig = build_figure(
        exp, {("a", "first-measure"): {"steps": [step], "stop_count": 2}}
    )
    lo, hi = fig.layout.yaxis.range
    assert lo <= 0.3 and hi >= 0.7


def test_configuration_failure_fails_worker(tmp_path, monkeypatch):
    exp = parse_config(dict(experiments=[ordinary()]))[0]

    def broken(*args):
        raise ConfigError("missing tool")

    monkeypatch.setattr(worker, "compute_cell", broken)
    with pytest.raises(ConfigError, match="missing tool"):
        worker.run_worker(exp, 0, tmp_path, tmp_path)


def test_files_kept_ranges_use_percentages():
    from experiment_runner.config import execution_plan, Experiment
    from experiment_runner.coverage_with_filter import PLOT_ROWS

    exp = execution_plan(Experiment("coverage", "coverage_with_filter", "Coverage", ("data",), ()))
    data = {
        "dataset_size": 200,
        "budgets": {},
        "adequacy": {tool: {metric: [80, 90] for metric in ("line", "mcdc", "joint")}
                     for tool, _, _ in PLOT_ROWS},
    }
    fig = build_figure(exp, {("data", "coverage"): data})
    axis = next(key for key in fig.layout if key.startswith("yaxis")
                and fig.layout[key].title.text == "Files kept (%)")
    fit, full = fig.layout.updatemenus[0].buttons
    assert full.args[0][axis + ".range"] == [0, 100]
    assert fit.args[0][axis + ".range"] == [39.75, 45.25]
