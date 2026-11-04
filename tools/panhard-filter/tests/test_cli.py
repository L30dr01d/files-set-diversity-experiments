from pathlib import Path

from panhard_filter.cli import main


def test_cli_prints_kept_names(tmp_path: Path, monkeypatch, capsys) -> None:
    files = tmp_path / "files"
    files.mkdir()
    (files / "a.txt").write_text("a", encoding="utf-8")
    (files / "b.txt").write_text("b", encoding="utf-8")

    monkeypatch.setattr(
        "panhard_filter.cli.filter",
        lambda files_dir: (
            ["a.txt", "b.txt"]
            if files_dir == files
            else (_ for _ in ()).throw(AssertionError(files_dir))
        ),
    )

    code = main([str(files)])
    assert code == 0
    captured = capsys.readouterr()
    assert captured.out == "a.txt\nb.txt\n"


def test_cli_missing_dir_exits_2(tmp_path: Path, capsys) -> None:
    missing = tmp_path / "missing"
    code = main([str(missing)])
    assert code == 2
    captured = capsys.readouterr()
    assert captured.out == ""
    assert captured.err == f"error: not a directory: {missing}\n"


def test_cli_filter_error_exits_1(tmp_path: Path, monkeypatch, capsys) -> None:
    files = tmp_path / "files"
    files.mkdir()
    (files / "a.txt").write_text("a", encoding="utf-8")

    def boom(*_args, **_kwargs):
        raise ValueError("panhard-xz ranking does not name the current files")

    monkeypatch.setattr("panhard_filter.cli.filter", boom)
    code = main([str(files)])
    assert code == 1
    captured = capsys.readouterr()
    assert captured.err == "error: panhard-xz ranking does not name the current files\n"
