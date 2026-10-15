from pathlib import Path

import pytest

from fast_filter.suite import list_test_files, write_suite_file


def test_list_test_files_sorts_by_basename(tmp_path: Path):
    (tmp_path / "b.txt").write_text("b", encoding="utf-8")
    (tmp_path / "a.txt").write_text("a", encoding="utf-8")
    names = [p.name for p in list_test_files(tmp_path)]
    assert names == ["a.txt", "b.txt"]


def test_list_test_files_rejects_empty(tmp_path: Path):
    with pytest.raises(ValueError):
        list_test_files(tmp_path)


def test_write_suite_file_flattens_newlines(tmp_path: Path):
    src = tmp_path / "files"
    src.mkdir()
    (src / "a.txt").write_text("line1\nline2\n", encoding="utf-8")
    dest = tmp_path / "suite.txt"
    write_suite_file(list_test_files(src), dest)
    assert dest.read_text(encoding="utf-8") == "line1 line2\n"
