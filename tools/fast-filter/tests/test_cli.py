from pathlib import Path

from fast_filter.cli import main


def test_cli_prints_kept_names(tmp_path: Path, monkeypatch, capsys):
    files = tmp_path / "files"
    files.mkdir()
    (files / "a.txt").write_text("a", encoding="utf-8")
    (files / "b.txt").write_text("b", encoding="utf-8")

    monkeypatch.setattr(
        "fast_filter.cli.reduce",
        lambda files_dir, algo, target_percent: (
            ["a.txt", "b.txt"]
            if (files_dir, algo, target_percent) == (files, "FAST++", 50.0)
            else (_ for _ in ()).throw(AssertionError((files_dir, algo, target_percent)))
        ),
    )

    code = main([str(files), "--algo", "FAST++", "--percent", "50"])
    assert code == 0
    captured = capsys.readouterr()
    assert captured.out == "a.txt\nb.txt\n"


def test_cli_missing_dir_exits_2(tmp_path: Path):
    code = main([str(tmp_path / "missing"), "--algo", "FAST++", "--percent", "50"])
    assert code == 2


def test_cli_unknown_algo_exits_2(tmp_path: Path):
    files = tmp_path / "files"
    files.mkdir()
    (files / "a.txt").write_text("a", encoding="utf-8")
    code = main([str(files), "--algo", "FAST-PW", "--percent", "50"])
    assert code == 2


def test_cli_reduce_error_exits_1(tmp_path: Path, monkeypatch):
    files = tmp_path / "files"
    files.mkdir()
    (files / "a.txt").write_text("a", encoding="utf-8")

    def boom(*_args, **_kwargs):
        raise ValueError("FAST-R kept 1 files, expected budget 2")

    monkeypatch.setattr("fast_filter.cli.reduce", boom)
    code = main([str(files), "--algo", "FAST++", "--percent", "50"])
    assert code == 1
