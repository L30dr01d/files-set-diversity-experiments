import importlib.util
from pathlib import Path

import pytest

SCRIPT = Path(__file__).resolve().parents[1] / "tools" / "copy_idr_flat.py"


def _load():
    spec = importlib.util.spec_from_file_location("copy_idr_flat", SCRIPT)
    assert spec is not None and spec.loader is not None
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def test_copies_idr_files_flat_into_prefix_with_count(tmp_path: Path):
    src = tmp_path / "proj"
    (src / "src" / "Lib").mkdir(parents=True)
    (src / "tests" / "empty-cons run 006").mkdir(parents=True)
    (src / "README.md").write_text("skip", encoding="utf-8")
    (src / "src" / "Lib" / "Main.idr").write_text("main", encoding="utf-8")
    (src / "tests" / "empty-cons run 006" / "DerivedGen.idr").write_text(
        "derived", encoding="utf-8"
    )
    (src / "tests" / "DerivedGen.idr").write_text("other", encoding="utf-8")
    dest_prefix = tmp_path / "datasets" / "031_deptycheck_original"

    dest = _load().copy_idr_flat(src, dest_prefix)

    assert dest == dest_prefix.parent / "031_deptycheck_original_3"
    names = sorted(p.name for p in dest.iterdir())
    assert names == [
        "src__Lib__Main.idr",
        "tests__DerivedGen.idr",
        "tests__empty-cons run 006__DerivedGen.idr",
    ]
    assert (dest / "src__Lib__Main.idr").read_text(encoding="utf-8") == "main"
    assert (dest / "tests__DerivedGen.idr").read_text(encoding="utf-8") == "other"
    assert (
        dest / "tests__empty-cons run 006__DerivedGen.idr"
    ).read_text(encoding="utf-8") == "derived"


def test_skips_git_directory(tmp_path: Path):
    src = tmp_path / "proj"
    (src / ".git" / "objects").mkdir(parents=True)
    (src / "src").mkdir()
    (src / ".git" / "objects" / "fake.idr").write_text("nope", encoding="utf-8")
    (src / "src" / "Main.idr").write_text("main", encoding="utf-8")
    dest_prefix = tmp_path / "out"

    dest = _load().copy_idr_flat(src, dest_prefix)

    assert dest.name == "out_1"
    assert [p.name for p in dest.iterdir()] == ["src__Main.idr"]


def test_fails_if_destination_exists(tmp_path: Path):
    src = tmp_path / "proj"
    src.mkdir()
    (src / "Main.idr").write_text("main", encoding="utf-8")
    dest_prefix = tmp_path / "out"
    existing = tmp_path / "out_1"
    existing.mkdir()
    (existing / "old.txt").write_text("keep", encoding="utf-8")

    with pytest.raises(FileExistsError):
        _load().copy_idr_flat(src, dest_prefix)

    assert (existing / "old.txt").read_text(encoding="utf-8") == "keep"
