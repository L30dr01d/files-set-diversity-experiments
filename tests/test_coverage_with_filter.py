from pathlib import Path

from experiment_runner.analyzer_coverage import ImageCoverage
from experiment_runner.config import Experiment


def test_failed_profile_export_warns_and_keeps_the_other_image(tmp_path: Path, monkeypatch, capsys) -> None:
    import json
    import subprocess

    from experiment_runner import coverage_with_filter as module

    profile_dir = tmp_path / "profiles"
    profile_dir.mkdir()
    (profile_dir / "ivl.profraw").write_bytes(b"bad")
    (profile_dir / "ivlpp.profraw").write_bytes(b"ok")
    ivl = tmp_path / "lib" / "ivl" / "ivl"
    ivlpp = tmp_path / "lib" / "ivl" / "ivlpp"
    ivl.parent.mkdir(parents=True)
    ivl.write_bytes(b"")
    ivlpp.write_bytes(b"")
    payload = {
        "data": [
            {
                "files": [
                    {
                        "filename": "parse.cc",
                        "segments": [[10, 1, 3, True, False, False]],
                        "mcdc_records": [],
                    }
                ]
            }
        ]
    }

    def fake_run(command, **kwargs):
        parts = [str(part) for part in command]
        if parts[0] == "llvm-profdata" and str(profile_dir / "ivl.profraw") in parts:
            return subprocess.CompletedProcess(parts, 1, "", "bad profile\n")
        if parts[0] == "llvm-profdata":
            return subprocess.CompletedProcess(parts, 0, "", "")
        assert "-skip-functions" in parts
        assert "-skip-expansions" in parts
        assert "-ignore-filename-regex=^/usr/|obj_dir" in parts
        assert "-num-threads=1" in parts
        kwargs["stdout"].write(json.dumps(payload).encode())
        return subprocess.CompletedProcess(parts, 0, "", "")

    monkeypatch.setattr(module.subprocess, "run", fake_run)
    coverage = module._coverage_from_profiles(
        profile_dir,
        ("ivlpp", "ivl"),
        {"ivl": ivl, "ivlpp": ivlpp},
        {},
    )
    assert coverage == {
        "ivlpp": ImageCoverage(
            line_hits=frozenset({"parse.cc:10"}),
            line_universe=frozenset({"parse.cc:10"}),
            mcdc_hits=frozenset(),
            mcdc_universe=frozenset(),
        ),
        "ivl": None,
    }
    err = capsys.readouterr().err
    assert f"warning: {ivl}: bad profile\n" in err
    assert "coverage: llvm-profdata ivl\n" in err
    export_bytes = len(json.dumps(payload).encode())
    assert f"coverage: llvm-cov ivlpp export {export_bytes} bytes\n" in err


def test_ci_times_the_export_and_reads_the_json_file(tmp_path: Path, monkeypatch, capsys) -> None:
    import json
    import subprocess

    from experiment_runner import coverage_with_filter as module

    monkeypatch.setenv("GITHUB_ACTIONS", "true")
    image = tmp_path / "verilator_bin"
    image.write_bytes(b"")
    profraw = tmp_path / "verilator_bin.profraw"
    profraw.write_bytes(b"raw")
    payload = {
        "data": [
            {
                "files": [
                    {
                        "filename": "V3Parse.cpp",
                        "segments": [[4, 1, 2, True, True, False]],
                        "mcdc_records": [],
                    },
                ]
            }
        ]
    }
    seen: list[list[str]] = []

    def fake_run(command, **kwargs):
        parts = [str(part) for part in command]
        seen.append(parts)
        if parts[0] == "llvm-profdata":
            return subprocess.CompletedProcess(parts, 0, "", "")
        kwargs["stdout"].write(json.dumps(payload).encode())
        return subprocess.CompletedProcess(
            parts,
            0,
            "",
            b"\tMaximum resident set size (kbytes): 42\n",
        )

    monkeypatch.setattr(module.subprocess, "run", fake_run)
    coverage = module._export_merged(image, [profraw])
    assert seen[1][:2] == ["/usr/bin/time", "-v"]
    assert seen[1][2] == "llvm-cov"
    assert "-skip-functions" in seen[1]
    assert coverage is not None
    assert coverage.line_hits == frozenset({"V3Parse.cpp:4"})
    assert "Maximum resident set size (kbytes): 42" in capsys.readouterr().err
    assert not (tmp_path / "verilator_bin.export.json").exists()


def test_assign_profraws_maps_learned_signature_and_exact_name() -> None:
    from experiment_runner import coverage_with_filter as module

    assign_profraws = getattr(module, "assign_profraws", None)
    assert assign_profraws is not None
    assigned = assign_profraws(
        [
            Path("1169_0.profraw"),
            Path("777_0.profraw"),
            Path("ivlpp.profraw"),
        ],
        {"1169_0": "ivl"},
    )
    assert assigned == {
        "ivl": [Path("1169_0.profraw")],
        "ivlpp": [Path("ivlpp.profraw")],
    }


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

    def fake_call(_fn, _args, *, timeout, memory_bytes=WORKER_MEMORY_BYTES):
        seen["memory_bytes"] = memory_bytes
        seen["timeout"] = timeout
        return {
            "verilator_bin": ImageCoverage(
                frozenset({"V3Parse.cpp:1"}),
                frozenset({"V3Parse.cpp:1"}),
                frozenset(),
                frozenset(),
            )
        }

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
            return None
        if analyzer == "iverilog" and len(paths) == 1:
            return _line_coverage(
                frozenset({"l", "late-image"}), frozenset({"l", "late-image"})
            )
        return ImageCoverage(
            frozenset({"l"}), frozenset({"l", "dormant"} if len(paths) == 2 else {"l"}),
            frozenset({"m"}), frozenset({"m"}),
        )

    def run_file(analyzer, source, directory):
        assert len(set_runs) == 80
        file_runs.append((analyzer, source.name))
        return _line_coverage(frozenset({"individual-only"}), frozenset({"individual-only"}))

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
        full_line = 100 / 3 if tool == "iverilog" else 50.0
        filtered = (
            {"line": 200 / 3, "mcdc": 0.0} if tool == "iverilog"
            else {"line": 50.0, "mcdc": 100.0}
        )
        assert budgets["100"] == [{"line": full_line, "mcdc": 100.0}] * 10
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
    assert axes[1].get_ylabel() == "Files kept"
    for axis, count in ((axes[1], 1), (axes[3], 0), (axes[14], 1)):
        bottom, top = axis.get_ylim()
        assert bottom < count < top
    assert (output / "coverage.png").is_file()
    assert (output / "coverage.svg").is_file()


def test_experiment_requires_one_dataset(tmp_path):
    from dataclasses import replace

    import pytest

    from experiment_runner.coverage_with_filter import run_coverage_with_filter

    for names in ((), ("ds_one", "ds_two")):
        experiment = replace(_coverage_experiment(), datasets=names)
        with pytest.raises(ValueError, match="exactly one dataset"):
            run_coverage_with_filter(experiment, tmp_path, output_dir=tmp_path / "output")


def _empty_set_measurement(*_args):
    return None


def test_unknown_draw_name_raises_before_the_figure(tmp_path: Path) -> None:
    import pytest

    from experiment_runner.coverage_with_filter import run_coverage_with_filter

    root = tmp_path / "repo"
    _write_two_sv_files(root)

    def reduce_fn(_files_dir: Path, _algo: str, _percent: float) -> list[str]:
        return ["missing.sv"]

    def adequate_fn(_suite: Path, _whitebox: Path) -> list[int]:
        return [1]

    def run_file(_analyzer: str, _source: Path, _profile_dir: Path) -> ImageCoverage:
        return _line_coverage(frozenset({"line:1"}), frozenset({"line:1"}))

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

    def run_file(analyzer: str, source: Path, _profile_dir: Path):
        if source.name == "second.sv":
            return None
        if analyzer == "iverilog":
            return ImageCoverage(
                line_hits=frozenset({"only-a"}),
                line_universe=frozenset({"only-a", "dormant"}),
                mcdc_hits=frozenset(),
                mcdc_universe=frozenset(),
            )
        return ImageCoverage(
            line_hits=frozenset({"vonly:1"}),
            line_universe=frozenset({"vonly:1"}),
            mcdc_hits=frozenset(),
            mcdc_universe=frozenset(),
        )

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


def _line_coverage(hits: frozenset[str], universe: frozenset[str]) -> ImageCoverage:
    return ImageCoverage(
        line_hits=hits,
        line_universe=universe,
        mcdc_hits=frozenset(),
        mcdc_universe=frozenset(),
    )


def test_calibration_falls_back_to_v_when_version_writes_two_profraws(tmp_path: Path, monkeypatch) -> None:
    from experiment_runner import coverage_with_filter as module

    _forbid_ensure_analyzers(monkeypatch, module)
    flags: list[str] = []

    def fake_run(command, profile_dir: Path) -> None:
        flags.append(command[-1])
        if command[-1] == "--version":
            (profile_dir / "one_0.profraw").write_bytes(b"a")
            (profile_dir / "two_0.profraw").write_bytes(b"b")
            return
        (profile_dir / "from_v_0.profraw").write_bytes(b"c")

    monkeypatch.setattr(module, "_run_analyzer", fake_run)
    assert module._calibrate_signature(tmp_path / "ivl") == "from_v_0"
    assert flags == ["-V"]


def test_calibration_returns_none_when_every_flag_writes_two_profraws(tmp_path: Path, monkeypatch) -> None:
    from experiment_runner import coverage_with_filter as module

    _forbid_ensure_analyzers(monkeypatch, module)
    flags: list[str] = []

    def fake_run(command, profile_dir: Path) -> None:
        flags.append(command[-1])
        tag = "v" if command[-1] == "-V" else "version"
        (profile_dir / f"{tag}_a.profraw").write_bytes(b"a")
        (profile_dir / f"{tag}_b.profraw").write_bytes(b"b")

    monkeypatch.setattr(module, "_run_analyzer", fake_run)
    assert module._calibrate_signature(tmp_path / "ivl") is None
    assert flags == ["-V", "--version"]


def test_launch_deletes_stale_profraw_before_the_analyzer_runs(tmp_path: Path, monkeypatch) -> None:
    import subprocess

    from experiment_runner import coverage_with_filter as module

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


def test_leftover_profraw_warns_with_the_image_and_the_name(tmp_path: Path, monkeypatch, capsys) -> None:
    import json
    import subprocess

    from experiment_runner import coverage_with_filter as module

    _forbid_ensure_analyzers(monkeypatch, module)
    profile_dir = tmp_path / "profiles"
    profile_dir.mkdir()
    (profile_dir / "ivl.profraw").write_bytes(b"ivl")
    (profile_dir / "ivlpp.profraw").write_bytes(b"ivlpp")
    (profile_dir / "extra_0.profraw").write_bytes(b"left")
    ivl = tmp_path / "ivl"
    ivlpp = tmp_path / "ivlpp"
    ivl.write_bytes(b"")
    ivlpp.write_bytes(b"")
    payload = {
        "data": [
            {
                "files": [
                    {
                        "filename": "parse.cc",
                        "segments": [[10, 1, 3, True, False, False]],
                        "mcdc_records": [],
                    }
                ]
            }
        ]
    }

    def fake_run(command, **kwargs):
        parts = [str(part) for part in command]
        if parts[0] == "llvm-profdata":
            return subprocess.CompletedProcess(parts, 0, "", "")
        kwargs["stdout"].write(json.dumps(payload).encode())
        return subprocess.CompletedProcess(parts, 0, "", "")

    monkeypatch.setattr(module.subprocess, "run", fake_run)
    module._coverage_from_profiles(
        profile_dir,
        ("ivlpp", "ivl"),
        {"ivl": ivl, "ivlpp": ivlpp},
        {},
    )
    err = capsys.readouterr().err
    assert f"warning: {ivlpp}: unmatched profraw extra_0.profraw\n" in err
    assert "coverage: llvm-cov ivl\n" in err


def test_missing_image_warns_when_the_profile_directory_is_not_empty(tmp_path: Path, monkeypatch, capsys) -> None:
    import json
    import subprocess

    from experiment_runner import coverage_with_filter as module

    _forbid_ensure_analyzers(monkeypatch, module)
    profile_dir = tmp_path / "profiles"
    profile_dir.mkdir()
    (profile_dir / "ivlpp.profraw").write_bytes(b"ok")
    (profile_dir / "999_0.profraw").write_bytes(b"left")
    ivl = tmp_path / "ivl"
    ivlpp = tmp_path / "ivlpp"
    ivl.write_bytes(b"")
    ivlpp.write_bytes(b"")
    payload = {
        "data": [
            {
                "files": [
                    {
                        "filename": "parse.cc",
                        "segments": [[10, 1, 1, True, False, False]],
                        "mcdc_records": [],
                    }
                ]
            }
        ]
    }

    def fake_run(command, **kwargs):
        parts = [str(part) for part in command]
        if parts[0] == "llvm-profdata":
            return subprocess.CompletedProcess(parts, 0, "", "")
        kwargs["stdout"].write(json.dumps(payload).encode())
        return subprocess.CompletedProcess(parts, 0, "", "")

    monkeypatch.setattr(module.subprocess, "run", fake_run)
    exports = module._coverage_from_profiles(
        profile_dir,
        ("ivlpp", "ivl"),
        {"ivl": ivl, "ivlpp": ivlpp},
        {},
    )
    assert exports["ivl"] is None
    assert exports["ivlpp"].line_hits == frozenset({"parse.cc:10"})
    err = capsys.readouterr().err
    assert f"warning: {ivl}: unmatched profraw 999_0.profraw\n" in err
    assert "coverage: llvm-cov ivlpp\n" in err


def test_empty_profile_directory_adds_no_hits_and_no_warning(tmp_path: Path, monkeypatch, capsys) -> None:
    from experiment_runner import coverage_with_filter as module

    _forbid_ensure_analyzers(monkeypatch, module)

    def fail(*_args, **_kwargs):
        raise AssertionError("llvm")

    monkeypatch.setattr(module.subprocess, "run", fail)
    profile_dir = tmp_path / "empty"
    profile_dir.mkdir()
    result = module._coverage_from_profiles(
        profile_dir,
        ("ivlpp", "ivl"),
        {"ivl": tmp_path / "ivl", "ivlpp": tmp_path / "ivlpp"},
        {},
    )
    assert result is None
    assert capsys.readouterr().err == ""


def test_later_failed_export_keeps_the_remembered_universe() -> None:
    from experiment_runner import coverage_with_filter as module

    ivl = ImageCoverage(
        line_hits=frozenset({"a:1"}),
        line_universe=frozenset({"a:1", "a:2"}),
        mcdc_hits=frozenset({"a:1:0"}),
        mcdc_universe=frozenset({"a:1:0", "a:1:1"}),
    )
    ivlpp = _line_coverage(frozenset(), frozenset())
    resolved = module._coverages_from_runs(
        [
            {"ivl": ivl, "ivlpp": ivlpp},
            {"ivl": None, "ivlpp": ivlpp},
        ]
    )
    assert resolved[0].line_hits == frozenset({"a:1"})
    assert resolved[0].mcdc_hits == frozenset({"a:1:0"})
    assert resolved[1].line_hits == frozenset()
    assert resolved[1].mcdc_hits == frozenset()
    assert resolved[1].line_universe == frozenset({"a:1", "a:2"})
    assert resolved[1].mcdc_universe == frozenset({"a:1:0", "a:1:1"})


def test_image_that_never_exports_raises_before_the_figure(tmp_path: Path) -> None:
    import pytest

    from experiment_runner.coverage_with_filter import run_coverage_with_filter

    root = tmp_path / "repo"
    _write_two_sv_files(root)
    _calls, reduce_fn = _budget_reduce()
    _whiteboxes, _suites, adequate_fn = _recording_adequate()

    def run_file(analyzer: str, _source: Path, _profile_dir: Path):
        if analyzer != "iverilog":
            return _line_coverage(frozenset({"v:1"}), frozenset({"v:1"}))
        return {
            "ivl": None,
            "ivlpp": _line_coverage(frozenset({"pp:1"}), frozenset({"pp:1"})),
        }

    output_dir = tmp_path / "output"
    with pytest.raises(RuntimeError, match="ivl"):
        run_coverage_with_filter(
            _coverage_experiment(),
            root,
            output_dir=output_dir,
            run_file=run_file,
            run_set=_empty_set_measurement,
            reduce_fn=reduce_fn,
            adequate_fn=adequate_fn,
        )
    assert not (output_dir / "coverage.png").is_file()


def test_returned_image_map_scores_the_file_that_exported(tmp_path: Path) -> None:
    from experiment_runner.coverage_with_filter import run_coverage_with_filter

    root = tmp_path / "repo"
    _write_two_sv_files(root)
    _calls, reduce_fn = _budget_reduce()
    _whiteboxes, _suites, adequate_fn = _recording_adequate()

    def run_file(analyzer: str, source: Path, _profile_dir: Path):
        if analyzer != "iverilog":
            return _line_coverage(frozenset({"v:1"}), frozenset({"v:1"}))
        if source.name == "first.sv":
            return {
                "ivl": _line_coverage(frozenset({"a:1"}), frozenset({"a:1", "a:2"})),
                "ivlpp": _line_coverage(frozenset(), frozenset()),
            }
        return {
            "ivl": None,
            "ivlpp": _line_coverage(frozenset(), frozenset()),
        }

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
    assert any(rows.splitlines() == ["La:1", ""] for rows in _whiteboxes)
    assert (output_dir / "coverage.png").is_file()


def test_compiler_env_builds_icarus_host_tools_with_clang(monkeypatch) -> None:
    from experiment_runner import coverage_with_filter as module

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


def test_set_merges_fresh_profiles_once_per_image(tmp_path, monkeypatch):
    from experiment_runner import coverage_with_filter as module

    images = {stem: tmp_path / stem for stem in ("ivlpp", "ivl")}
    monkeypatch.setattr(module, "ensure_analyzers", lambda: (tmp_path / "iverilog", tmp_path / "verilator"))
    monkeypatch.setattr(module, "_find_installed", lambda _prefix, stem: images[stem])
    monkeypatch.setattr(module, "_image_signature", lambda image: image.name)
    launched = []

    def launch(command, directory):
        launched.append(Path(command[-1]).name)
        for stem in images:
            (directory / f"{stem}.profraw").touch()

    def timed(fn, args, **kwargs):
        result = fn(*args)
        return None if args[1].name == "timeout.sv" else result

    exports = []
    coverage = ImageCoverage(frozenset({"l"}), frozenset({"l"}), frozenset({"m"}), frozenset({"m"}))

    def export(image, raws):
        exports.append((image.name, raws))
        return coverage

    monkeypatch.setattr(module, "_run_analyzer", launch)
    monkeypatch.setattr(module, "call_timed", timed)
    monkeypatch.setattr(module, "_export_merged", export)
    (tmp_path / "ivl.profraw").touch()
    assert module.default_run_set(
        "iverilog", [Path(name) for name in ("a.sv", "timeout.sv", "b.sv")], tmp_path, 120
    ) == coverage
    assert launched == ["a.sv", "timeout.sv", "b.sv"]
    assert [stem for stem, _ in exports] == ["ivlpp", "ivl"]
    for stem, raws in exports:
        assert [raw.name for raw in raws] == [f"{stem}.profraw"] * 2
        assert len({raw.parent for raw in raws}) == 2
        assert all(raw.parent != tmp_path for raw in raws)
    assert module.default_run_set("iverilog", [], tmp_path, 120) == module._NO_HITS
    assert len(exports) == 2


def test_adequacy_counts_use_goal_and_tool_specific_hits(tmp_path):
    from experiment_runner import coverage_with_filter as module

    paths = sorted(_write_two_sv_files(tmp_path).glob("*.sv"))
    hits = frozenset({"shared"})
    empty = frozenset()
    line = _line_coverage(hits, hits)
    mcdc = ImageCoverage(empty, empty, hits, hits)
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
