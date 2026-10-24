from pathlib import Path

import pytest

from panhard_measure import score
from panhard_measure.score import score as score_fn


def test_score_parses_script_stdout_and_passes_sorted_files(tmp_path: Path) -> None:
    files_dir = tmp_path / "files"
    files_dir.mkdir()
    (files_dir / "b.txt").write_text("b")
    (files_dir / "a.txt").write_text("a")
    args_log = tmp_path / "args.txt"
    script = tmp_path / "fake-panhard"
    script.write_text(
        "#!/bin/bash\n"
        f"printf '%s\\n' \"$@\" > '{args_log}'\n"
        "echo '0.250000'\n"
    )
    script.chmod(0o755)
    assert score(files_dir, script=script) == 0.25
    assert args_log.read_text().splitlines() == [
        str(files_dir / "a.txt"),
        str(files_dir / "b.txt"),
    ]


def test_score_rejects_empty_directory(tmp_path: Path) -> None:
    with pytest.raises(ValueError, match="no regular files"):
        score(tmp_path)


def test_score_rejects_missing_path(tmp_path: Path) -> None:
    with pytest.raises(ValueError, match="not a directory"):
        score(tmp_path / "missing")


def test_vendored_script_exists_and_is_executable() -> None:
    script = Path(score_fn.__code__.co_filename).resolve().parent / "panhard-xz"
    assert script.is_file()
    assert script.stat().st_mode & 0o111
