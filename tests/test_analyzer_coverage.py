from pathlib import Path

from experiment_runner.analyzer_coverage import (
    ImageCoverage,
    adequate_tick,
    combine_images,
    hits_from_llvm_export,
    iverilog_command,
    profile_env,
    subset_percents,
    verilator_command,
    whitebox_line,
)


def test_shared_line_counts_once():
    universe = ImageCoverage(
        line_universe=frozenset({"a:1", "a:2"}),
        line_hits=frozenset(),
        mcdc_universe=frozenset({"a:1:0"}),
        mcdc_hits=frozenset(),
    )
    first = ImageCoverage(
        line_hits=frozenset({"a:1"}),
        line_universe=universe.line_universe,
        mcdc_hits=frozenset(),
        mcdc_universe=universe.mcdc_universe,
    )
    second = ImageCoverage(
        line_hits=frozenset({"a:1"}),
        line_universe=universe.line_universe,
        mcdc_hits=frozenset({"a:1:0"}),
        mcdc_universe=universe.mcdc_universe,
    )
    line, mcdc = subset_percents([first, second], universe)
    assert line == 50.0
    assert mcdc == 100.0


def test_empty_universe_percent_is_zero():
    universe = ImageCoverage(
        line_hits=frozenset(),
        line_universe=frozenset(),
        mcdc_hits=frozenset(),
        mcdc_universe=frozenset({"a:1:0"}),
    )
    covered = ImageCoverage(
        line_hits=frozenset({"a:1"}),
        line_universe=frozenset(),
        mcdc_hits=frozenset({"a:1:0"}),
        mcdc_universe=frozenset({"a:1:0"}),
    )
    line, mcdc = subset_percents([covered], universe)
    assert line == 0.0
    assert mcdc == 100.0


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


def test_whitebox_line_attaches_the_letter_to_the_id():
    coverage = ImageCoverage(
        line_hits=frozenset({"a:1"}),
        line_universe=frozenset({"a:1", "a:9"}),
        mcdc_hits=frozenset({"a:1:0"}),
        mcdc_universe=frozenset({"a:1:0", "a:9:1"}),
    )
    assert whitebox_line(coverage) == "La:1 Ma:1:0"


def test_whitebox_line_sorts_lines_before_decisions():
    coverage = ImageCoverage(
        line_hits=frozenset({"b:2", "a:1"}),
        line_universe=frozenset(),
        mcdc_hits=frozenset({"c:3:1", "a:1:0"}),
        mcdc_universe=frozenset(),
    )
    assert whitebox_line(coverage) == "La:1 Lb:2 Ma:1:0 Mc:3:1"


def test_combine_images_unions_each_field():
    first = ImageCoverage(
        line_hits=frozenset({"a:1"}),
        line_universe=frozenset({"a:1"}),
        mcdc_hits=frozenset({"a:1:0"}),
        mcdc_universe=frozenset({"a:1:0"}),
    )
    second = ImageCoverage(
        line_hits=frozenset({"b:2"}),
        line_universe=frozenset({"b:2", "b:3"}),
        mcdc_hits=frozenset({"b:2:1"}),
        mcdc_universe=frozenset({"b:2:1"}),
    )
    combined = combine_images([first, second])
    assert combined == ImageCoverage(
        line_hits=frozenset({"a:1", "b:2"}),
        line_universe=frozenset({"a:1", "b:2", "b:3"}),
        mcdc_hits=frozenset({"a:1:0", "b:2:1"}),
        mcdc_universe=frozenset({"a:1:0", "b:2:1"}),
    )


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


def test_llvm_export_drops_generated_models_and_zero_counts():
    # Segment: [line, col, count, hasCount, isRegionEntry, isGapRegion]
    # MC/DC: conditions are the first list of bools. Each condition id is
    # basename:line:column:index in that list. A false flag stays in the universe.
    payload = {
        "data": [
            {
                "files": [
                    {
                        "filename": "parse.cc",
                        "segments": [
                            [10, 1, 3, True, False, False],
                            [11, 1, 0, True, True, False],
                            [12, 1, 8, True, True, True],
                        ],
                        "mcdc_records": [
                            [10, 1, 10, 8, 0, 0, 0, 0, 0, [True, False], [{"exec": 0}]],
                            [11, 4, 11, 9, 3, 1, [False, False], [{"exec": 1}]],
                        ],
                    },
                    {
                        "filename": "/tmp/obj_dir/Vtop.cpp",
                        "segments": [[4, 1, 7, True, True, False]],
                        "mcdc_records": [
                            [4, 1, 4, 2, 1, 1, 0, 0, 0, [True], []],
                        ],
                    },
                ]
            }
        ]
    }
    coverage = hits_from_llvm_export(payload)
    assert coverage.line_hits == frozenset({"parse.cc:10"})
    assert coverage.line_universe == frozenset({"parse.cc:10", "parse.cc:11"})
    assert coverage.mcdc_hits == frozenset({"parse.cc:10:1:0"})
    assert coverage.mcdc_universe == frozenset(
        {
            "parse.cc:10:1:0",
            "parse.cc:10:1:1",
            "parse.cc:11:4:0",
            "parse.cc:11:4:1",
        }
    )
    ids = (
        coverage.line_hits
        | coverage.line_universe
        | coverage.mcdc_hits
        | coverage.mcdc_universe
    )
    assert all("Vtop" not in hit_id for hit_id in ids)
    assert "parse.cc:12" not in ids
