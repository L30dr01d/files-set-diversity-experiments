import importlib
import sys
import types
from pathlib import Path

import pytest

from fast_filter import reduce


def test_reduce_unknown_algo(tmp_path: Path):
    (tmp_path / "a.txt").write_text("a", encoding="utf-8")
    with pytest.raises(ValueError, match="Unknown algo"):
        reduce(tmp_path, algo="FAST-PW", target_percent=50)


def test_reduce_maps_one_based_ids(tmp_path: Path, monkeypatch):
    (tmp_path / "a.txt").write_text("a", encoding="utf-8")
    (tmp_path / "b.txt").write_text("b", encoding="utf-8")
    (tmp_path / "c.txt").write_text("c", encoding="utf-8")
    (tmp_path / "d.txt").write_text("d", encoding="utf-8")

    def fake_fast_pw(suite, r=1, b=10, bbox=True, k=5, memory=True, B=None):
        assert B == 2
        assert str(suite).endswith("suite.txt")
        return None, None, [1, 3]  # 1-based → a.txt, c.txt

    fake_fastr = types.ModuleType("fastr")
    fake_fastr.fast_pw = fake_fast_pw
    monkeypatch.setitem(sys.modules, "fastr", fake_fastr)

    kept = reduce(tmp_path, algo="FAST-pw", target_percent=50)
    assert kept == ["a.txt", "c.txt"]


def test_reduce_rejects_wrong_count(tmp_path: Path, monkeypatch):
    (tmp_path / "a.txt").write_text("a", encoding="utf-8")
    (tmp_path / "b.txt").write_text("b", encoding="utf-8")
    (tmp_path / "c.txt").write_text("c", encoding="utf-8")
    (tmp_path / "d.txt").write_text("d", encoding="utf-8")

    reduce_mod = importlib.import_module("fast_filter.reduce")

    monkeypatch.setattr(reduce_mod, "_run_inadequate", lambda algo, suite, budget: [1])
    with pytest.raises(ValueError, match="budget"):
        reduce(tmp_path, algo="FAST++", target_percent=50)
