from pathlib import Path

from experiment_runner.analyzer_coverage import (
    adequate_tick,
    iverilog_command,
    profile_env,
    verilator_command,
)


def test_adequate_tick_is_share_of_the_dataset():
    assert adequate_tick(25, 50) == "adequate\n25 files, 50%"


def test_adequate_axis_label_matches_the_single_tick():
    from experiment_runner.analyzer_coverage import adequate_axis_label, adequate_tick

    samples = [{"kept": 25, "total": 50}]
    assert adequate_axis_label(samples) == adequate_tick(25, 50)


def test_adequate_axis_label_ranges_files_and_percents():
    from experiment_runner.analyzer_coverage import adequate_axis_label

    assert adequate_axis_label(
        [{"kept": 25, "total": 50}, {"kept": 10, "total": 50}]
    ) == "adequate\n10-25 files, 20-50%"


def test_adequate_axis_label_collapses_a_tied_side():
    from experiment_runner.analyzer_coverage import adequate_axis_label

    assert adequate_axis_label(
        [{"kept": 10, "total": 50}, {"kept": 10, "total": 40}]
    ) == "adequate\n10 files, 20-25%"
    assert adequate_axis_label(
        [{"kept": 1, "total": 3}, {"kept": 2, "total": 6}]
    ) == "adequate\n1-2 files, 33%"


def test_adequate_axis_label_treats_a_zero_total_as_zero_percent():
    from experiment_runner.analyzer_coverage import adequate_axis_label

    assert adequate_axis_label([{"kept": 0, "total": 0}]) == "adequate\n0 files, 0%"
    assert adequate_axis_label(
        [{"kept": 0, "total": 0}, {"kept": 1, "total": 2}]
    ) == "adequate\n0-1 files, 0-50%"


def test_analyzer_commands_compile_without_running():
    iverilog = iverilog_command(
        Path("/bin/iverilog"), Path("/tmp/d.sv"), Path("/tmp/a.out")
    )
    verilator = verilator_command(
        Path("/bin/verilator"), Path("/tmp/d.sv"), Path("/tmp/obj")
    )
    assert iverilog == ["/bin/iverilog", "-g2012", "-o", "/tmp/a.out", "/tmp/d.sv"]
    assert verilator == [
        "/bin/verilator",
        "--cc",
        "--timing",
        "-Wno-fatal",
        "+1800-2023ext+sv",
        "--Mdir",
        "/tmp/obj",
        "/tmp/d.sv",
    ]
    forbidden = ("vvp", "--exe", "--build", "--binary")
    for command in (iverilog, verilator):
        assert all(flag not in command for flag in forbidden)


def test_profile_env_writes_profraw_into_the_directory():
    profile_file = profile_env(Path("/tmp/p"))["LLVM_PROFILE_FILE"]
    assert profile_file == "/tmp/p/%m.profraw"
    assert profile_file.endswith("/%m.profraw")
