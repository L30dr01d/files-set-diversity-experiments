from random_filter.stop import should_stop


def test_stop_pct_none_does_not_stop():
    assert should_stop([5, 5, 5, 5, 5], file_count=10, stop_pct=None, min_stop_rounds=1) is False


def test_too_few_rounds_does_not_stop():
    assert should_stop([0, 1, 2], file_count=6, stop_pct=0.03, min_stop_rounds=5) is False


def test_quartiles_inside_epsilon_stop():
    knees = [5] * 20
    assert should_stop(knees, file_count=10, stop_pct=0.03, min_stop_rounds=20) is True


def test_quartiles_outside_epsilon_do_not_stop():
    assert should_stop([0, 1, 2, 3, 40], file_count=6, stop_pct=0.03, min_stop_rounds=5) is False


def test_zero_stop_pct_uses_a_strict_quartile_test():
    assert should_stop([10, 10, 10, 10], file_count=100, stop_pct=0.0, min_stop_rounds=4) is False
