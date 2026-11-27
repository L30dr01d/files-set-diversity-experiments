from pathlib import Path

from experiment_runner.config import Experiment


def _mock_file_export(tmp_path, monkeypatch, report, status=0):
    import sys
    from experiment_runner import instrumented_analyzers as module

    images = {"ivlpp": tmp_path / "ivlpp", "ivl": tmp_path / "ivl"}
    monkeypatch.setattr(module, "_analyzer_images", lambda _: (tmp_path / "iverilog", images))
    monkeypatch.setattr(module, "_profile_source", lambda _tool, _src, directory, _exe: (directory / "a.profraw").touch())

    def command(objects, raws, directory):
        assert objects == list(images.values())
        assert raws == [directory / "a.profraw"]
        script = f"import sys; sys.stdout.write({report!r}); sys.exit({status})"
        return [sys.executable, "-c", script]

    monkeypatch.setattr(module, "_export_command", command)
    return module


def test_per_input_hits_preserve_selector_ids(tmp_path, monkeypatch):
    import json

    covered = [10, 1, 1, True, True, False]
    report = {"data": [{"files": [
        {"filename": "/src/a.cc", "segments": [
            covered, covered, [11, 1, 0, True, True, False], [12, 1, 1, True, True, True],
        ], "mcdc_records": [[13, 2, 13, 10, 0, 0, [True, False, True]]]},
        {"filename": "/obj_dir/gen.cc", "segments": [covered], "mcdc_records": []},
    ]}]}
    module = _mock_file_export(tmp_path, monkeypatch, json.dumps(report))
    path = module.default_run_file("iverilog", tmp_path / "a.sv", tmp_path)
    assert list(tmp_path.iterdir()) == [path]
    assert path.read_text().splitlines() == ["La.cc:10", "Ma.cc:13:2:0", "Ma.cc:13:2:2"]


def test_completed_adequacy_run_requires_a_raw_profile(tmp_path, monkeypatch):
    import pytest

    module = _mock_file_export(tmp_path, monkeypatch, "")
    monkeypatch.setattr(module, "_profile_source", lambda *_: True)
    with pytest.raises(RuntimeError, match="iverilog produced no profile for .*a.sv"):
        module.default_run_file("iverilog", tmp_path / "a.sv", tmp_path)
    assert not list(tmp_path.iterdir())


def test_per_input_export_and_extractor_failures_propagate(tmp_path, monkeypatch):
    import subprocess
    import pytest

    for report, status in [('{"data":[{"files":[]}]}', 17), ("malformed", 0), ("", 0)]:
        module = _mock_file_export(tmp_path, monkeypatch, report, status)
        with pytest.raises(subprocess.CalledProcessError):
            module.default_run_file("iverilog", tmp_path / "a.sv", tmp_path)


def test_each_design_times_out_after_two_minutes() -> None:
    import inspect

    from experiment_runner.coverage_with_filter import DESIGN_TIMEOUT_SECONDS
    from experiment_runner.coverage_with_filter import run_coverage_with_filter

    assert DESIGN_TIMEOUT_SECONDS == 120
    parameter = inspect.signature(run_coverage_with_filter).parameters["timeout"]
    assert parameter.default == 120


def test_each_design_is_logged(tmp_path: Path, capsys) -> None:
    from experiment_runner.coverage_with_filter import _stored_profiles
    from experiment_runner.timeout import hang_reduce

    _stored_profiles("iverilog", [tmp_path / "a.sv"], hang_reduce, tmp_path / "profiles", 0.4)
    err = capsys.readouterr().err
    assert "a.sv" in err
    assert "timed out" in err


def test_stored_profiles_does_not_apply_the_score_memory_cap(tmp_path: Path, monkeypatch) -> None:
    from experiment_runner import coverage_with_filter as module
    from experiment_runner.timeout import WORKER_MEMORY_BYTES

    seen = {}

    def fake_call(_fn, _args, *, timeout, memory_bytes=WORKER_MEMORY_BYTES, raise_errors):
        seen["memory_bytes"] = memory_bytes
        seen["timeout"] = timeout
        assert raise_errors
        return tmp_path / "hits.txt"

    monkeypatch.setattr(module, "call_timed", fake_call)
    module._stored_profiles(
        "verilator", [tmp_path / "a.sv"], lambda *_args: None, tmp_path / "profiles", 120
    )
    assert seen["timeout"] == 120
    assert seen["memory_bytes"] is None


def test_run_coverage_with_filter_defaults_to_default_run_file() -> None:
    import inspect

    from experiment_runner import coverage_with_filter as module

    default_run_file = getattr(module, "default_run_file", None)
    parameter = inspect.signature(module.run_coverage_with_filter).parameters["run_file"]
    assert parameter.default is default_run_file
    assert default_run_file is not None


def _coverage_experiment() -> Experiment:
    return Experiment(
        id="coverage",
        type="coverage_with_filter",
        title="Viewer title",
        datasets=("ds_one",),
        tools=("fast-filter",),
    )


def _write_two_sv_files(root: Path) -> Path:
    dataset = root / "datasets" / "ds_one"
    dataset.mkdir(parents=True)
    # Written out of basename order so list_test_files sorting is observable.
    (dataset / "second.sv").write_text("beta\n", encoding="utf-8")
    (dataset / "first.sv").write_text("alpha\n", encoding="utf-8")
    return dataset


def _budget_reduce():
    calls: list[tuple[Path, str, int]] = []

    def reduce_fn(files_dir: Path, algo: str, percent: int) -> list[str]:
        calls.append((files_dir, algo, percent))
        names = sorted(p.name for p in files_dir.iterdir() if p.is_file())
        return names[:1]

    return calls, reduce_fn


def _recording_adequate():
    whiteboxes: list[str] = []
    suites: list[str] = []

    def adequate_fn(suite_path: Path, whitebox_path: Path) -> list[int]:
        suites.append(suite_path.read_text(encoding="utf-8"))
        whiteboxes.append(whitebox_path.read_text(encoding="utf-8"))
        return [1]

    return whiteboxes, suites, adequate_fn


def test_fresh_budget_draws_measure_both_metrics_and_render_layout(tmp_path, monkeypatch):
    from matplotlib.axes import Axes

    from experiment_runner.coverage_with_filter import run_coverage_with_filter

    dataset = _write_two_sv_files(tmp_path)
    calls = []
    set_runs = []
    file_runs = []
    plotted = []
    boxplot = Axes.boxplot

    def record_boxes(ax, samples, **kwargs):
        plotted.append((ax, samples))
        return boxplot(ax, samples, **kwargs)

    monkeypatch.setattr(Axes, "boxplot", record_boxes)

    def reduce_fn(files_dir, algo, percent):
        assert (files_dir, algo) == (dataset, "FAST++")
        calls.append(percent)
        return ["first.sv" if len(calls) % 2 else "second.sv"]

    def run_set(analyzer, paths, directory, timeout):
        assert timeout == 120
        set_runs.append((analyzer, tuple(path.name for path in paths), directory))
        if paths[0].name == "second.sv":
            return {"line": 0.0, "mcdc": 0.0}
        if analyzer == "iverilog" and len(paths) == 1:
            return {"line": 66.67, "mcdc": 0.0}
        return {"line": 50.0, "mcdc": 100.0}

    def run_file(analyzer, source, directory):
        assert len(set_runs) == 80
        file_runs.append((analyzer, source.name))
        hits = directory / "hits.txt"
        hits.write_text("Lindividual-only\n")
        return hits

    output = tmp_path / "output"
    results = run_coverage_with_filter(
        _coverage_experiment(), tmp_path, output_dir=output, run_file=run_file,
        run_set=run_set, reduce_fn=reduce_fn, adequate_fn=lambda *_: [1],
    )
    assert calls == [75] * 10 + [50] * 10 + [25] * 10
    assert len(set_runs) == len({directory for _, _, directory in set_runs}) == 80
    assert file_runs == [
        (tool, name) for tool in ("iverilog", "verilator") for name in ("first.sv", "second.sv")
    ]
    for index in range(0, 80, 2):
        first, second = set_runs[index:index + 2]
        assert {first[0], second[0]} == {"iverilog", "verilator"}
        assert first[1] == second[1]
        if index < 20:
            assert first[1] == ("first.sv", "second.sv")
    for tool, budgets in results["budgets"].items():
        assert list(budgets) == ["100", "75", "50", "25"]
        filtered = (
            {"line": 66.67, "mcdc": 0.0} if tool == "iverilog"
            else {"line": 50.0, "mcdc": 100.0}
        )
        assert budgets["100"] == [{"line": 50.0, "mcdc": 100.0}] * 10
        for budget in ("75", "50", "25"):
            assert budgets[budget] == [filtered, {"line": 0.0, "mcdc": 0.0}] * 5
    assert results["adequacy"] == {
        tool: {"line": [1] * 10, "mcdc": [0] * 10, "joint": [1] * 10}
        for tool in ("verilator", "iverilog", "both")
    }

    axes = plotted[0][0].figure.axes
    assert len(axes) == 15
    assert [index for index, ax in enumerate(axes) if not ax.get_visible()] == [10, 12]
    assert [len(samples) for _, samples in plotted] == [4, 1, 4, 1, 1] * 2 + [1, 1, 1]
    assert all(len(draws) == 10 for _, samples in plotted for draws in samples)
    assert [tick.get_text() for tick in axes[0].get_xticklabels()] == ["100%", "75%", "50%", "25%"]
    assert axes[1].get_ylabel() == "Files kept (%)"
    assert [axes[i].get_ylim() for i in (0, 2, 5, 7)] == [
        (-3, 53), (-5, 105), (-4, 71), (-5, 105),
    ]
    assert {axes[i].get_ylim() for i in (1, 3, 4, 6, 8, 9, 11, 13, 14)} == {(-3, 53)}
    assert plotted[1][1] == [[50.0] * 10]
    assert plotted[3][1] == [[0.0] * 10]
    assert (output / "coverage.png").is_file()
    assert (output / "coverage.svg").is_file()


def test_plot_zooms_in_on_narrow_and_constant_samples():
    import matplotlib.pyplot as plt

    from experiment_runner.coverage_with_filter import (
        BUDGET_PERCENTS,
        plot_coverage_bars,
    )

    results = {
        "budgets": {
            tool: {str(p): [{"line": 83.2, "mcdc": 86.1}] for p in BUDGET_PERCENTS}
            for tool in ("verilator", "iverilog")
        },
        "adequacy": {
            tool: {"line": [1], "mcdc": [1], "joint": [1]}
            for tool in ("verilator", "iverilog", "both")
        },
    }
    figure = plot_coverage_bars(results, _coverage_experiment(), dataset_size=4)
    try:
        assert figure.get_suptitle() == "Viewer title (ds_one)"
        assert figure.axes[0].get_ylim() == (82, 84)
        assert figure.axes[2].get_ylim() == (85, 87)
        assert figure.axes[1].get_ylim() == (24, 26)
    finally:
        plt.close(figure)


def test_experiment_requires_one_dataset(tmp_path):
    from dataclasses import replace

    import pytest

    from experiment_runner.coverage_with_filter import run_coverage_with_filter

    for names in ((), ("ds_one", "ds_two")):
        experiment = replace(_coverage_experiment(), datasets=names)
        with pytest.raises(ValueError, match="exactly one dataset"):
            run_coverage_with_filter(experiment, tmp_path, output_dir=tmp_path / "output")


def _empty_set_measurement(*_args):
    return {"line": 0.0, "mcdc": 0.0}


def test_unknown_draw_name_raises_before_the_figure(tmp_path: Path) -> None:
    import pytest

    from experiment_runner.coverage_with_filter import run_coverage_with_filter

    root = tmp_path / "repo"
    _write_two_sv_files(root)

    def reduce_fn(_files_dir: Path, _algo: str, _percent: float) -> list[str]:
        return ["missing.sv"]

    def adequate_fn(_suite: Path, _whitebox: Path) -> list[int]:
        return [1]

    def run_file(*_args):
        raise AssertionError("adequacy ran before budget validation")

    with pytest.raises(ValueError, match="unknown kept basename"):
        run_coverage_with_filter(
            _coverage_experiment(),
            root,
            output_dir=tmp_path / "output",
            run_file=run_file,
            run_set=_empty_set_measurement,
            reduce_fn=reduce_fn,
            adequate_fn=adequate_fn,
        )
    assert not (tmp_path / "output" / "coverage.png").is_file()


def test_missing_profile_adds_no_hits_and_writes_the_figure(tmp_path: Path) -> None:
    from experiment_runner.coverage_with_filter import run_coverage_with_filter

    root = tmp_path / "repo"
    _write_two_sv_files(root)
    _calls, reduce_fn = _budget_reduce()
    whiteboxes, _suites, adequate_fn = _recording_adequate()

    def run_file(analyzer: str, source: Path, directory: Path):
        hits = directory / "hits.txt"
        text = "Lonly-a\n" if analyzer == "iverilog" else "Lvonly:1\n"
        hits.write_text(text if source.name == "first.sv" else "")
        return hits

    output_dir = tmp_path / "output"
    results = run_coverage_with_filter(
        _coverage_experiment(),
        root,
        output_dir=output_dir,
        run_file=run_file,
        run_set=_empty_set_measurement,
        reduce_fn=reduce_fn,
        adequate_fn=adequate_fn,
    )

    assert results["adequacy"]["iverilog"]["line"] == [1] * 10
    iverilog_box = next(text for text in whiteboxes if "only-a" in text)
    assert iverilog_box.splitlines()[1].split() == []
    png = output_dir / "coverage.png"
    assert png.is_file()
    assert png.with_suffix(".svg").is_file()


def test_all_missing_profiles_score_zero_and_write_the_figure(tmp_path: Path) -> None:
    from experiment_runner.coverage_with_filter import run_coverage_with_filter

    root = tmp_path / "repo"
    _write_two_sv_files(root)
    _calls, reduce_fn = _budget_reduce()
    _whiteboxes, _suites, adequate_fn = _recording_adequate()

    def run_file(_analyzer: str, _source: Path, _profile_dir: Path):
        return None

    output_dir = tmp_path / "output"
    results = run_coverage_with_filter(
        _coverage_experiment(),
        root,
        output_dir=output_dir,
        run_file=run_file,
        run_set=_empty_set_measurement,
        reduce_fn=reduce_fn,
        adequate_fn=adequate_fn,
    )

    for analyzer in ("iverilog", "verilator"):
        assert results["budgets"][analyzer]["100"] == [{"line": 0.0, "mcdc": 0.0}] * 10
        assert results["adequacy"][analyzer]["joint"] == [0] * 10
    png = output_dir / "coverage.png"
    assert png.is_file()
    assert png.with_suffix(".svg").is_file()


def _forbid_ensure_analyzers(monkeypatch, module) -> None:
    def fail(*_args, **_kwargs):
        raise AssertionError("ensure_analyzers")

    monkeypatch.setattr(module, "ensure_analyzers", fail)


def test_analyzer_timeout_stops_child_process(tmp_path: Path) -> None:
    import sys
    import time

    from experiment_runner import instrumented_analyzers as module

    started = tmp_path / "started"
    survived = tmp_path / "survived"
    child = (
        "import time; from pathlib import Path; "
        f"Path({str(started)!r}).touch(); time.sleep(2); Path({str(survived)!r}).touch()"
    )
    parent = (
        "import subprocess, sys, time; "
        f"subprocess.Popen([sys.executable, '-c', {child!r}]); time.sleep(4)"
    )

    before = time.monotonic()
    assert module._run_analyzer([sys.executable, "-c", parent], tmp_path, timeout=1) is False
    assert time.monotonic() - before < 3
    assert started.exists()
    time.sleep(2)
    assert not survived.exists()


def test_launch_deletes_stale_profraw_before_the_analyzer_runs(tmp_path: Path, monkeypatch) -> None:
    import subprocess

    from experiment_runner import instrumented_analyzers as module

    _forbid_ensure_analyzers(monkeypatch, module)
    profile_dir = tmp_path / "first.sv"
    profile_dir.mkdir()
    stale = profile_dir / "sig_0.profraw"
    stale.write_bytes(b"old")

    def fake_run(command, **_kwargs):
        assert list(profile_dir.glob("*.profraw")) == []
        return subprocess.CompletedProcess(command, 0)

    monkeypatch.setattr(module.subprocess, "run", fake_run)
    module._run_analyzer([str(tmp_path / "iverilog")], profile_dir)
    assert list(profile_dir.glob("*.profraw")) == []


def _failed_file(*_):
    raise RuntimeError("could not extract hit IDs")


def test_adequacy_worker_failure_propagates(tmp_path: Path):
    import pytest

    from experiment_runner.coverage_with_filter import _stored_profiles

    for failed in (_failed_file, lambda *args: _failed_file(*args)):
        with pytest.raises(RuntimeError, match="extract hit IDs"):
            _stored_profiles("iverilog", [tmp_path / "a.sv"], failed, tmp_path, 5)


def test_compiler_env_builds_icarus_host_tools_with_clang(monkeypatch) -> None:
    from experiment_runner import instrumented_analyzers as module

    monkeypatch.delenv("CC_FOR_BUILD", raising=False)
    monkeypatch.setenv("CFLAGS", "-O2")
    env = module._compiler_env()
    assert env["CC"] == "clang"
    assert env["CXX"] == "clang++"
    assert env["CC_FOR_BUILD"] == "clang"
    assert env["CFLAGS"].startswith("-O2 ")
    for name in ("CFLAGS", "CXXFLAGS", "LDFLAGS"):
        assert "-fprofile-instr-generate" in env[name]
        assert "-fcoverage-mapping" in env[name]
        assert "-fcoverage-mcdc" in env[name]


def test_set_summarizes_all_fresh_profiles_from_completed_designs(tmp_path, monkeypatch):
    from experiment_runner import instrumented_analyzers as module

    images = {stem: tmp_path / stem for stem in ("ivlpp", "ivl")}
    monkeypatch.setattr(module, "_analyzer_images", lambda _: (tmp_path / "iverilog", images))
    launched = []

    def launch(analyzer, source, directory, executable, *, timeout):
        assert timeout == 120
        launched.append(source.name)
        for stem in images:
            (directory / f"{stem}.profraw").touch()
        return source.name != "timeout.sv"

    summaries = []
    coverage = {"line": 12.34, "mcdc": 5.67}

    def summary(objects, raws, directory):
        assert objects == list(images.values())
        assert all(raw.is_file() and raw.parent.parent == directory for raw in raws)
        summaries.append([(raw.parent.name, raw.name) for raw in raws])
        return coverage

    monkeypatch.setattr(module, "_profile_source", launch)
    monkeypatch.setattr(module, "_summary", summary)
    (tmp_path / "stale.profraw").touch()
    sources = [Path(name) for name in ("a.sv", "timeout.sv", "b.sv")]
    assert module.default_run_set("iverilog", sources, tmp_path, 120) == coverage
    assert launched == [source.name for source in sources]
    assert summaries == [[(index, name) for index in ("0", "2")
                          for name in ("ivl.profraw", "ivlpp.profraw")]]
    for no_data in ([], [Path("timeout.sv")]):
        assert module.default_run_set("iverilog", no_data, tmp_path, 120) == coverage
    assert summaries[1:] == [[], []]


def test_adequacy_counts_use_goal_and_tool_specific_hits(tmp_path):
    from experiment_runner import coverage_with_filter as module

    paths = sorted(_write_two_sv_files(tmp_path).glob("*.sv"))
    line, mcdc = tmp_path / "line.txt", tmp_path / "mcdc.txt"
    line.write_text("Lshared\n")
    mcdc.write_text("Mshared\n")
    observed = {}

    def select(suite, whitebox):
        assert suite.read_text().splitlines() == ["alpha", "beta"]
        rows = [set(row.split()) for row in whitebox.read_text().splitlines()]
        observed.setdefault((whitebox.parent.parent.name, whitebox.parent.name), []).append(rows)
        return [idx for idx, row in enumerate(rows, 1) if row]

    counts = module._adequate_counts(
        paths, {"verilator": [line, mcdc], "iverilog": [mcdc, line]}, select, tmp_path / "work"
    )
    assert counts == {
        "verilator": {"line": [1] * 10, "mcdc": [1] * 10, "joint": [2] * 10},
        "iverilog": {"line": [1] * 10, "mcdc": [1] * 10, "joint": [2] * 10},
        "both": {"line": [2] * 10, "mcdc": [2] * 10, "joint": [2] * 10},
    }
    assert observed["both", "line"] == [[{"Lverilator:shared"}, {"Liverilog:shared"}]] * 10
    assert observed["both", "mcdc"] == [[{"Miverilog:shared"}, {"Mverilator:shared"}]] * 10
    assert observed["both", "joint"] == [
        [{"Lverilator:shared", "Miverilog:shared"}, {"Liverilog:shared", "Mverilator:shared"}]
    ] * 10

    observed.clear()
    counts = module._adequate_counts(
        paths, {"verilator": [mcdc, mcdc], "iverilog": [mcdc, line]}, select, tmp_path / "work"
    )
    assert counts["verilator"]["line"] == [0] * 10
    assert ("verilator", "line") not in observed
