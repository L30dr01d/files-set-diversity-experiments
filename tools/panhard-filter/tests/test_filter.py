from pathlib import Path

import pytest

from panhard_filter import filter
from panhard_filter.filter import filter as filter_fn


def _files(tmp_path: Path, names: tuple[str, ...]) -> Path:
    files_dir = tmp_path / "files"
    files_dir.mkdir()
    for name in names:
        (files_dir / name).write_text(name, encoding="utf-8")
    return files_dir


def _script(tmp_path: Path, body: str) -> Path:
    script = tmp_path / "fake-panhard"
    script.write_text("#!/bin/bash\n" + body, encoding="utf-8")
    script.chmod(0o755)
    return script


def _resolved(files_dir: Path, name: str) -> str:
    return str((files_dir / name).resolve())


def test_filter_undoes_drop_when_score_falls(tmp_path: Path) -> None:
    files_dir = _files(tmp_path, ("b.txt", "a.txt", "c.txt"))
    args_log = tmp_path / "args.txt"
    a = _resolved(files_dir, "a.txt")
    b = _resolved(files_dir, "b.txt")
    c = _resolved(files_dir, "c.txt")
    script = _script(
        tmp_path,
        f"printf '%s\\n' \"$@\" >> '{args_log}'\n"
        f'if grep -Fqx -- "{c}" <<<"$(printf \'%s\\n\' "$@")"; then\n'
        "  echo 0.5\n"
        f'  echo "0.9 {a}" >&2\n'
        f'  echo "0.8 {b}" >&2\n'
        f'  echo "0.1 {c}" >&2\n'
        "else\n"
        "  echo 0.4\n"
        f'  echo "0.7 {a}" >&2\n'
        f'  echo "0.6 {b}" >&2\n'
        "fi\n",
    )
    assert filter(files_dir, script=script) == ["a.txt", "b.txt", "c.txt"]
    calls = args_log.read_text().splitlines()
    assert calls[:4] == ["--verbose", a, b, c]
    assert calls[4:7] == ["--verbose", a, b]


def test_filter_continues_when_score_is_equal(tmp_path: Path) -> None:
    files_dir = _files(tmp_path, ("a.txt", "b.txt", "c.txt"))
    args_log = tmp_path / "args.txt"
    a = _resolved(files_dir, "a.txt")
    b = _resolved(files_dir, "b.txt")
    c = _resolved(files_dir, "c.txt")
    script = _script(
        tmp_path,
        f"printf '%s\\n' \"$@\" >> '{args_log}'\n"
        f'if grep -Fqx -- "{c}" <<<"$(printf \'%s\\n\' "$@")"; then\n'
        "  echo 0.5\n"
        f'  echo "0.2 {c}" >&2\n'
        f'  echo "0.9 {a}" >&2\n'
        f'  echo "0.8 {b}" >&2\n'
        f'elif grep -Fqx -- "{b}" <<<"$(printf \'%s\\n\' "$@")"; then\n'
        "  echo 0.5\n"
        f'  echo "0.1 {b}" >&2\n'
        f'  echo "0.9 {a}" >&2\n'
        "else\n"
        "  echo 0.5\n"
        "fi\n",
    )
    assert filter(files_dir, script=script) == ["a.txt"]
    calls = args_log.read_text().splitlines()
    assert calls[-2:] == ["--verbose", a]


def test_filter_undoes_last_drop_when_one_file_score_falls(tmp_path: Path) -> None:
    files_dir = _files(tmp_path, ("a.txt", "b.txt"))
    a = _resolved(files_dir, "a.txt")
    b = _resolved(files_dir, "b.txt")
    script = _script(
        tmp_path,
        f'if grep -Fqx -- "{b}" <<<"$(printf \'%s\\n\' "$@")"; then\n'
        "  echo 0.5\n"
        f'  echo "0.1 {b}" >&2\n'
        f'  echo "0.9 {a}" >&2\n'
        "else\n"
        "  echo 0\n"
        "fi\n",
    )
    assert filter(files_dir, script=script) == ["a.txt", "b.txt"]


def test_filter_parses_bc_ranking_lines(tmp_path: Path) -> None:
    files_dir = _files(tmp_path, ("a.txt", "b.txt"))
    a = _resolved(files_dir, "a.txt")
    b = _resolved(files_dir, "b.txt")
    script = _script(
        tmp_path,
        f'if grep -Fqx -- "{b}" <<<"$(printf \'%s\\n\' "$@")"; then\n'
        "  echo ' .5000000000'\n"
        f'  echo " .0000000000 {a}" >&2\n'
        f'  echo " 0.1000000000 {b}" >&2\n'
        "else\n"
        "  echo 0.5\n"
        "fi\n",
    )
    assert filter(files_dir, script=script) == ["b.txt"]


def test_filter_tie_breaks_by_basename(tmp_path: Path) -> None:
    files_dir = _files(tmp_path, ("b.txt", "a.txt"))
    a = _resolved(files_dir, "a.txt")
    b = _resolved(files_dir, "b.txt")
    script = _script(
        tmp_path,
        f'if grep -Fqx -- "{a}" <<<"$(printf \'%s\\n\' "$@")" && '
        f'grep -Fqx -- "{b}" <<<"$(printf \'%s\\n\' "$@")"; then\n'
        "  echo 0.5\n"
        f'  echo "0.1 {b}" >&2\n'
        f'  echo "0.1 {a}" >&2\n'
        "else\n"
        "  echo 0.5\n"
        "fi\n",
    )
    assert filter(files_dir, script=script) == ["b.txt"]


def test_filter_one_file_does_not_call_script(tmp_path: Path) -> None:
    files_dir = _files(tmp_path, ("only.txt",))
    args_log = tmp_path / "args.txt"
    script = _script(
        tmp_path,
        f"printf '%s\\n' \"$@\" > '{args_log}'\n"
        "echo 0.0\n",
    )
    assert filter(files_dir, script=script) == ["only.txt"]
    assert not args_log.exists()


def test_filter_rejects_empty_directory(tmp_path: Path) -> None:
    with pytest.raises(ValueError, match="no regular files"):
        filter(tmp_path)


def test_filter_rejects_missing_path(tmp_path: Path) -> None:
    with pytest.raises(ValueError, match="not a directory"):
        filter(tmp_path / "missing")


def test_filter_rejects_ranking_outside_current_set(tmp_path: Path) -> None:
    files_dir = _files(tmp_path, ("a.txt", "b.txt"))
    a = _resolved(files_dir, "a.txt")
    outsider = _resolved(tmp_path, "nope.txt")
    script = _script(
        tmp_path,
        "echo 0.5\n"
        f'echo "0.2 {outsider}" >&2\n'
        f'echo "0.9 {a}" >&2\n',
    )
    with pytest.raises(ValueError, match="ranking"):
        filter(files_dir, script=script)


def test_filter_rejects_non_numeric_score(tmp_path: Path) -> None:
    files_dir = _files(tmp_path, ("a.txt", "b.txt"))
    a = _resolved(files_dir, "a.txt")
    b = _resolved(files_dir, "b.txt")
    script = _script(
        tmp_path,
        "echo not-a-score\n"
        f'echo "0.2 {a}" >&2\n'
        f'echo "0.9 {b}" >&2\n',
    )
    with pytest.raises(ValueError, match="score"):
        filter(files_dir, script=script)


def test_filter_rejects_non_numeric_contribution(tmp_path: Path) -> None:
    files_dir = _files(tmp_path, ("a.txt", "b.txt"))
    a = _resolved(files_dir, "a.txt")
    b = _resolved(files_dir, "b.txt")
    script = _script(
        tmp_path,
        "echo 0.5\n"
        f'echo "low {a}" >&2\n'
        f'echo "0.9 {b}" >&2\n',
    )
    with pytest.raises(ValueError, match="contribution"):
        filter(files_dir, script=script)


def test_vendored_script_exists_and_is_executable() -> None:
    script = Path(filter_fn.__code__.co_filename).resolve().parent / "panhard-xz"
    assert script.is_file()
    assert script.stat().st_mode & 0o111
