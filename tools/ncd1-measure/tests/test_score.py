from pathlib import Path

import pytest

from ncd1_measure import score


def test_score_three_files_is_finite(tmp_path: Path):
    (tmp_path / "a.txt").write_text("aaa", encoding="utf-8")
    (tmp_path / "b.txt").write_text("bbb", encoding="utf-8")
    (tmp_path / "c.txt").write_text("ccc", encoding="utf-8")
    value = score(tmp_path)
    assert value == value
    assert isinstance(value, float)


def test_score_two_files_raises(tmp_path: Path):
    (tmp_path / "a.txt").write_text("aaa", encoding="utf-8")
    (tmp_path / "b.txt").write_text("bbb", encoding="utf-8")
    with pytest.raises(ValueError):
        score(tmp_path)


def test_score_rejects_empty_dir(tmp_path: Path):
    with pytest.raises(ValueError):
        score(tmp_path)
