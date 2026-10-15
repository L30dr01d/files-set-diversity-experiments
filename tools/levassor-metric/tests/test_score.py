from pathlib import Path

import pytest

from levassor_metric import score

_BLOB = bytes(range(256)) * 4


def _write_copies(folder: Path, blob: bytes, n: int) -> None:
    for i in range(n):
        (folder / f"f{i:03d}.bin").write_bytes(blob)


def test_score_two_files_raises(tmp_path: Path) -> None:
    (tmp_path / "a.txt").write_text("aaa", encoding="utf-8")
    (tmp_path / "b.txt").write_text("bbb", encoding="utf-8")
    with pytest.raises(ValueError, match="levassor_metric requires >= 3 files"):
        score(tmp_path)


def test_score_rejects_empty_dir(tmp_path: Path) -> None:
    with pytest.raises(ValueError, match="no regular files"):
        score(tmp_path)


def test_score_rejects_missing_path(tmp_path: Path) -> None:
    with pytest.raises(ValueError, match="not a directory"):
        score(tmp_path / "missing")


def test_score_ignores_subdirectories(tmp_path: Path) -> None:
    (tmp_path / "a.txt").write_text("a", encoding="utf-8")
    (tmp_path / "b.txt").write_text("b", encoding="utf-8")
    (tmp_path / "c.txt").write_text("c", encoding="utf-8")
    (tmp_path / "sub").mkdir()
    (tmp_path / "sub" / "d.txt").write_text("d", encoding="utf-8")
    value = score(tmp_path)
    assert 0.0 <= value <= 1.0
    assert isinstance(value, float)


def test_score_valid_suite_is_unit_interval(tmp_path: Path) -> None:
    _write_copies(tmp_path, _BLOB, 3)
    value = score(tmp_path)
    assert 0.0 <= value <= 1.0
    assert isinstance(value, float)


def test_identical_copies_fall_toward_one_over_n(tmp_path: Path) -> None:
    three = tmp_path / "n3"
    ten = tmp_path / "n10"
    three.mkdir()
    ten.mkdir()
    _write_copies(three, _BLOB, 3)
    _write_copies(ten, _BLOB, 10)
    score_3 = score(three)
    score_10 = score(ten)
    assert score_10 < score_3
    assert score_3 == pytest.approx(1 / 3, rel=0.2)
    assert score_10 == pytest.approx(1 / 10, rel=0.2)


def test_unrelated_files_score_higher_than_near_copies(tmp_path: Path) -> None:
    near = tmp_path / "near"
    far = tmp_path / "far"
    near.mkdir()
    far.mkdir()
    for i in range(3):
        edited = bytearray(_BLOB)
        edited[i] ^= 0xFF
        (near / f"n{i}.bin").write_bytes(bytes(edited))
        (far / f"f{i}.bin").write_bytes(bytes(b ^ ((i + 1) * 17) for b in _BLOB))
    assert score(far) > score(near)


def test_three_empty_files_score_zero(tmp_path: Path) -> None:
    (tmp_path / "a").write_bytes(b"")
    (tmp_path / "b").write_bytes(b"")
    (tmp_path / "c").write_bytes(b"")
    assert score(tmp_path) == 0.0
