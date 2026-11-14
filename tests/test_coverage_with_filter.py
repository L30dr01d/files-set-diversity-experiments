from pathlib import Path

from experiment_runner.analyzer_coverage import ImageCoverage
from experiment_runner.config import Experiment
from experiment_runner.coverage_with_filter import plot_coverage_bars


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


def _score(line: float, mcdc: float, kept: int = 1, total: int = 50) -> dict:
    return {"line": line, "mcdc": mcdc, "kept": kept, "total": total}


def _repeated(line: float, mcdc: float) -> list[dict]:
    return [_score(line, mcdc) for _ in range(10)]


def test_plot_labels_adequate_share(tmp_path: Path) -> None:
    import matplotlib

    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    from matplotlib.colors import to_rgba
    from matplotlib.patches import PathPatch, Rectangle

    experiment = Experiment(
        id="coverage",
        type="coverage_with_filter",
        title="Viewer title",
        datasets=("ds_one",),
        tools=("fast-filter",),
    )
    icarus_adequate = _repeated(10.0, 10.0)
    icarus_adequate[-1] = _score(80.0, 80.0)
    icarus = {
        "100": _score(40.0, 40.0, kept=50, total=50),
        "75": _repeated(30.0, 30.0),
        "50": _repeated(20.0, 20.0),
        "25": _repeated(10.0, 10.0),
        "adequate": icarus_adequate,
    }
    verilator = {
        "100": _score(40.0, 40.0, kept=50, total=50),
        "75": _repeated(30.0, 30.0),
        "50": _repeated(20.0, 20.0),
        "25": _repeated(10.0, 10.0),
        "adequate": _repeated(40.0, 40.0),
    }
    fig = plot_coverage_bars(
        {"ds_one": {"iverilog": icarus, "verilator": verilator}},
        experiment,
    )
    try:
        assert fig._suptitle.get_text() == "Viewer title"
        assert [ax.get_title() for ax in fig.axes] == [
            "ds_one\nLine coverage",
            "ds_one\nMC/DC",
        ]
        expected_ticks = ["100%", "75%", "50%", "25%", "adequate"]
        for ax in fig.axes:
            assert ax.get_ylabel() == "%"
            assert [tick.get_text() for tick in ax.get_xticklabels()] == expected_ticks
            assert sum(isinstance(patch, Rectangle) for patch in ax.patches) == 2
            assert sum(isinstance(patch, PathPatch) for patch in ax.patches) == 8
            assert [text.get_text() for text in ax.get_legend().get_texts()] == [
                "Icarus",
                "Verilator",
            ]
            fliers = [line for line in ax.lines if line.get_marker() == "o"]
            assert any(len(line.get_xdata()) for line in fliers)
            horizontal = [
                to_rgba(line.get_color())
                for line in ax.lines
                if len(line.get_ydata()) == 2 and line.get_ydata()[0] == line.get_ydata()[1]
            ]
            assert to_rgba("C1") not in horizontal
        png = tmp_path / "coverage.png"
        svg = png.with_suffix(".svg")
        fig.savefig(png)
        fig.savefig(svg)
        assert png.is_file()
        assert svg.is_file()
    finally:
        plt.close(fig)


def test_plot_names_each_dataset_row() -> None:
    import matplotlib

    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    from matplotlib.patches import PathPatch

    experiment = Experiment(
        id="coverage",
        type="coverage_with_filter",
        title="Viewer title",
        datasets=("ds_one", "ds_two"),
        tools=("fast-filter",),
    )

    def cells() -> dict:
        return {
            "100": _score(40.0, 40.0, kept=50, total=50),
            "75": _repeated(30.0, 30.0),
            "50": _repeated(20.0, 20.0),
            "25": _repeated(10.0, 10.0),
            "adequate": _repeated(40.0, 40.0),
        }

    fig = plot_coverage_bars(
        {
            "ds_one": {"iverilog": cells(), "verilator": cells()},
            "ds_two": {"iverilog": cells(), "verilator": cells()},
        },
        experiment,
    )
    try:
        assert [ax.get_title() for ax in fig.axes] == [
            "ds_one\nLine coverage",
            "ds_one\nMC/DC",
            "ds_two\nLine coverage",
            "ds_two\nMC/DC",
        ]
        for ax in fig.axes:
            assert sum(isinstance(patch, PathPatch) for patch in ax.patches) == 8
    finally:
        plt.close(fig)


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


def test_percent_draws_are_shared_and_coverage_runs_once(tmp_path: Path) -> None:
    from experiment_runner.coverage_with_filter import run_coverage_with_filter

    root = tmp_path / "repo"
    _write_two_sv_files(root)
    calls: list[float] = []
    runs: list[tuple[str, str]] = []

    def reduce_fn(files_dir: Path, algo: str, percent: float) -> list[str]:
        assert algo == "FAST++"
        assert files_dir == root / "datasets" / "ds_one"
        calls.append(percent)
        names = sorted(p.name for p in files_dir.iterdir() if p.is_file())
        return [names[0] if len(calls) % 3 == 1 else names[1]]

    def adequate_fn(_suite_path: Path, whitebox_path: Path) -> list[int]:
        text = whitebox_path.read_text(encoding="utf-8")
        return [1] if "icarus-only" in text else [2]

    def run_file(analyzer: str, source: Path, _profile_dir: Path) -> ImageCoverage:
        runs.append((analyzer, source.name))
        if analyzer == "iverilog":
            hit = frozenset({"icarus-only"}) if source.name == "first.sv" else frozenset()
            return _line_coverage(hit, frozenset({"icarus-only"}))
        hit = frozenset({"verilator-only"}) if source.name == "second.sv" else frozenset()
        return _line_coverage(hit, frozenset({"verilator-only"}))

    results = run_coverage_with_filter(
        _coverage_experiment(),
        root,
        output_dir=tmp_path / "output",
        run_file=run_file,
        reduce_fn=reduce_fn,
        adequate_fn=adequate_fn,
    )
    assert len(runs) == 4
    assert calls == [75] * 10 + [50] * 10 + [25] * 10
    icarus = [item["line"] for item in results["ds_one"]["iverilog"]["75"]]
    verilator = [item["line"] for item in results["ds_one"]["verilator"]["75"]]
    assert icarus == [100.0, 0.0, 0.0, 100.0, 0.0, 0.0, 100.0, 0.0, 0.0, 100.0]
    assert verilator == [0.0 if value == 100.0 else 100.0 for value in icarus]
    assert [item["line"] for item in results["ds_one"]["verilator"]["adequate"]] == [100.0] * 10
    assert results["ds_one"]["iverilog"]["100"]["line"] == 100.0
    assert len(results["ds_one"]["iverilog"]["adequate"]) == 10


def test_each_dataset_is_filtered_on_its_own_files(tmp_path: Path) -> None:
    from experiment_runner.coverage_with_filter import run_coverage_with_filter

    root = tmp_path / "repo"
    dirs = []
    for name, stem in (("ds_one", "a.sv"), ("ds_two", "b.sv")):
        directory = root / "datasets" / name
        directory.mkdir(parents=True)
        (directory / stem).write_text(stem, encoding="utf-8")
        dirs.append(directory)
    seen: list[Path] = []

    def reduce_fn(files_dir: Path, _algo: str, _percent: float) -> list[str]:
        seen.append(files_dir)
        return [next(files_dir.iterdir()).name]

    def adequate_fn(_suite: Path, _whitebox: Path) -> list[int]:
        return [1]

    def run_file(_analyzer: str, _source: Path, _profile_dir: Path) -> ImageCoverage:
        return _line_coverage(frozenset({"line:1"}), frozenset({"line:1"}))

    experiment = Experiment(
        id="coverage",
        type="coverage_with_filter",
        title="Viewer title",
        datasets=("ds_one", "ds_two"),
        tools=("fast-filter",),
    )
    run_coverage_with_filter(
        experiment,
        root,
        output_dir=tmp_path / "output",
        run_file=run_file,
        reduce_fn=reduce_fn,
        adequate_fn=adequate_fn,
    )
    assert seen[:30] == [dirs[0]] * 30
    assert seen[30:] == [dirs[1]] * 30


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
            reduce_fn=reduce_fn,
            adequate_fn=adequate_fn,
        )
    assert not (tmp_path / "output" / "coverage.png").is_file()


def test_shared_line_is_counted_once_and_adequate_keeps_one_file(tmp_path: Path) -> None:
    from experiment_runner.coverage_with_filter import run_coverage_with_filter

    root = tmp_path / "repo"
    dataset = _write_two_sv_files(root)
    calls, reduce_fn = _budget_reduce()
    whiteboxes, suites, adequate_fn = _recording_adequate()

    def run_file(analyzer: str, source: Path, _profile_dir: Path) -> ImageCoverage:
        if analyzer == "iverilog" and source.name == "first.sv":
            return ImageCoverage(
                line_hits=frozenset({"shared:1"}),
                line_universe=frozenset({"shared:1"}),
                mcdc_hits=frozenset({"dec:1:0"}),
                mcdc_universe=frozenset({"dec:1:0"}),
            )
        if analyzer == "iverilog":
            return ImageCoverage(
                line_hits=frozenset({"shared:1"}),
                line_universe=frozenset({"shared:1"}),
                mcdc_hits=frozenset(),
                mcdc_universe=frozenset({"dec:1:0"}),
            )
        if source.name == "first.sv":
            return ImageCoverage(
                line_hits=frozenset({"vfirst:1"}),
                line_universe=frozenset({"vfirst:1"}),
                mcdc_hits=frozenset(),
                mcdc_universe=frozenset(),
            )
        return ImageCoverage(
            line_hits=frozenset({"vsecond:1"}),
            line_universe=frozenset({"vsecond:1", "vextra:1", "vextra:2"}),
            mcdc_hits=frozenset(),
            mcdc_universe=frozenset(),
        )

    output_dir = tmp_path / "output"
    results = run_coverage_with_filter(
        _coverage_experiment(),
        root,
        output_dir=output_dir,
        run_file=run_file,
        reduce_fn=reduce_fn,
        adequate_fn=adequate_fn,
    )

    assert [(algo, percent) for _files, algo, percent in calls] == (
        [("FAST++", 75)] * 10 + [("FAST++", 50)] * 10 + [("FAST++", 25)] * 10
    )
    assert {files for files, _algo, _percent in calls} == {dataset}
    icarus = results["ds_one"]["iverilog"]
    verilator = results["ds_one"]["verilator"]
    # Two files hit the same line. Counting each file would make this 200.
    assert icarus["100"]["line"] == 100.0
    assert icarus["100"]["mcdc"] == 100.0
    # The dropped file's line stays in the denominator, so one kept hit is 25.
    assert verilator["100"]["line"] == 50.0
    assert [item["line"] for item in verilator["75"]] == [25.0] * 10
    assert [item["line"] for item in verilator["50"]] == [25.0] * 10
    assert [item["line"] for item in verilator["25"]] == [25.0] * 10
    # Id 1 is the first basename. That file is the only MC/DC hit.
    assert [item["mcdc"] for item in icarus["adequate"]] == [100.0] * 10
    assert [item["mcdc"] for item in icarus["75"]] == [100.0] * 10
    for cells in (icarus, verilator):
        assert cells["100"]["kept"] == 2
        assert cells["100"]["total"] == 2
        for category in ("75", "50", "25", "adequate"):
            assert [item["kept"] for item in cells[category]] == [1] * 10
            assert [item["total"] for item in cells[category]] == [2] * 10
    assert len(whiteboxes) == 20
    assert len(set(whiteboxes)) == 2
    iverilog_box = next(
        text for text in whiteboxes if any(token.startswith("M") for token in text.split())
    )
    second_tokens = iverilog_box.splitlines()[1].split()
    assert any(token.startswith("L") for token in second_tokens)
    assert all(not token.startswith("M") for token in second_tokens)
    assert suites[whiteboxes.index(iverilog_box)] == "alpha\nbeta\n"
    png = output_dir / "coverage.png"
    assert png.is_file()
    assert png.with_suffix(".svg").is_file()


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
        reduce_fn=reduce_fn,
        adequate_fn=adequate_fn,
    )

    # dormant stays in the universe and is not a hit from the missing file.
    assert results["ds_one"]["iverilog"]["100"]["line"] == 50.0
    assert results["ds_one"]["iverilog"]["100"]["total"] == 2
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
        reduce_fn=reduce_fn,
        adequate_fn=adequate_fn,
    )

    for analyzer in ("iverilog", "verilator"):
        assert results["ds_one"][analyzer]["100"]["line"] == 0.0
        assert results["ds_one"][analyzer]["100"]["mcdc"] == 0.0
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
        reduce_fn=reduce_fn,
        adequate_fn=adequate_fn,
    )
    assert results["ds_one"]["iverilog"]["100"]["line"] == 50.0
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
