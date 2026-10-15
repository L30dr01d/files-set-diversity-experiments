import pytest

from fast_filter.budget import budget_from_percent


def test_budget_half_of_ten():
    assert budget_from_percent(10, 50) == 5


def test_budget_floors():
    assert budget_from_percent(3, 50) == 1


def test_budget_rejects_zero_result():
    with pytest.raises(ValueError):
        budget_from_percent(1, 10)


def test_budget_rejects_empty_suite():
    with pytest.raises(ValueError):
        budget_from_percent(0, 50)


def test_budget_rejects_bad_percent():
    with pytest.raises(ValueError):
        budget_from_percent(10, 0)
    with pytest.raises(ValueError):
        budget_from_percent(10, 101)
