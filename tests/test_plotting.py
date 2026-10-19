from experiment_runner.plotting import tool_color


def test_known_measures_keep_fixed_cycle_slots():
    assert tool_color("panhard-v3-measure", 3) == "C0"
    assert tool_color("levassor-measure", 0) == "C1"
    assert tool_color("poisson-measure", 0) == "C2"
    assert tool_color("ncd1-measure", 0) == "C3"


def test_unknown_measure_uses_index():
    assert tool_color("fake-measure", 0) == "C0"
    assert tool_color("other-measure", 1) == "C1"
