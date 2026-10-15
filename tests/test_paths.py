from pathlib import Path

import pytest

from experiment_runner.config import ConfigError
from experiment_runner.paths import dataset_dir, load_score, tool_dir, tool_module_name


def test_dataset_dir_joins_datasets(tmp_path: Path):
    assert dataset_dir(tmp_path, "016_algos_java_1_task_10_variants_10") == (
        tmp_path / "datasets" / "016_algos_java_1_task_10_variants_10"
    )


def test_tool_dir_joins_tools(tmp_path: Path):
    assert tool_dir(tmp_path, "levassor-metric") == tmp_path / "tools" / "levassor-metric"


def test_tool_module_name_replaces_hyphens():
    assert tool_module_name("panhard-v3-metric") == "panhard_v3_metric"
    assert tool_module_name("levassor-metric") == "levassor_metric"


def test_load_score_returns_levassor_callable():
    fn = load_score("levassor-metric")
    assert callable(fn)
    assert fn.__module__.startswith("levassor_metric")


def test_load_score_missing_module_raises():
    with pytest.raises(ConfigError, match="no-such-metric"):
        load_score("no-such-metric")


def test_load_score_without_score_attr_raises(monkeypatch):
    import sys
    import types

    mod = types.ModuleType("blank_metric")
    monkeypatch.setitem(sys.modules, "blank_metric", mod)
    with pytest.raises(ConfigError, match="no score"):
        load_score("blank-metric")
