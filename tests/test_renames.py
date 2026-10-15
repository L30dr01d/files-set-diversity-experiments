import importlib
import pytest


def test_levassor_metric_imports_score():
    from levassor_metric import score

    assert callable(score)


def test_new_metric_is_gone():
    with pytest.raises(ImportError):
        importlib.import_module("new_metric")


def test_fast_filter_imports_reduce():
    from fast_filter import ALGOS, budget_from_percent, reduce

    assert callable(reduce)
    assert callable(budget_from_percent)
    assert ALGOS


def test_fast_reducer_is_gone():
    with pytest.raises(ImportError):
        importlib.import_module("fast_reducer")
