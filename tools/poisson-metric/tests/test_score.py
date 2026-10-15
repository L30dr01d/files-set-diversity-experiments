from pathlib import Path

import pytest

from poisson_metric import score


def test_score_two_files_is_finite(tmp_path: Path):
    (tmp_path / "a.txt").write_text("hello world\n", encoding="utf-8")
    (tmp_path / "b.txt").write_text("hello there\n", encoding="utf-8")
    value = score(tmp_path)
    assert value == value  # not NaN
    assert isinstance(value, float)


def test_score_rejects_missing_dir(tmp_path: Path):
    with pytest.raises(ValueError):
        score(tmp_path / "nope")


def test_score_rejects_empty_dir(tmp_path: Path):
    with pytest.raises(ValueError):
        score(tmp_path)
