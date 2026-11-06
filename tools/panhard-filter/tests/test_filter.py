import stat
import subprocess
from pathlib import Path

from panhard_filter.cli import main
from panhard_filter.filter import filter_dir, filter_paths

ROOT = Path(__file__).resolve().parents[3]
REAL = ROOT / "tools/panhard-filter/src/panhard_filter/panhard-xz"
DATASET = ROOT / "datasets/007_algos_java_5_tasks_10_variants_50"


def _script(tmp_path: Path, body: str) -> Path:
    path = tmp_path / "fake-panhard"
    path.write_text(body, encoding="utf-8")
    path.chmod(path.stat().st_mode | stat.S_IEXEC)
    return path


def _fake(tmp_path: Path) -> Path:
    # Scores by file count. Importance is the trailing integer in the name.
    return _script(
        tmp_path,
        """#!/bin/sh
if [ "$1" = "--verbose" ]; then shift; fi
n=0
for f in "$@"; do n=$((n + 1)); done
echo "scale=10; $n / 10" | bc
for f in "$@"; do
  echo "1 $f" >&2
done
""",
    )


def test_stops_when_diversity_drops(tmp_path: Path):
    folder = tmp_path / "data"
    folder.mkdir()
    for name in ("a_3", "b_1", "c_2", "d_9"):
        (folder / name).write_text(name)
    # fake score is count/10, so it never drops. Use a script that drops at 3.
    script = _script(
        tmp_path,
        """#!/bin/sh
if [ "$1" = "--verbose" ]; then shift; fi
n=0
for f in "$@"; do n=$((n + 1)); done
if [ "$n" -le 3 ]; then echo "0.1"; else echo "0.$n"; fi
for f in "$@"; do echo "1 $f" >&2; done
""",
    )
    result = filter_dir(folder, script=script)
    assert result.stop_count == 3
    assert len(result.kept) == 3
    assert [step.remaining_count for step in result.steps] == [4, 3]


def test_dont_stop_filters_to_two_and_keeps_stop_count(tmp_path: Path):
    folder = tmp_path / "data"
    folder.mkdir()
    for name in ("a", "b", "c", "d"):
        (folder / name).write_text(name)
    script = _script(
        tmp_path,
        """#!/bin/sh
if [ "$1" = "--verbose" ]; then shift; fi
n=0
for f in "$@"; do n=$((n + 1)); done
if [ "$n" -le 3 ]; then echo "0.1"; else echo "0.$n"; fi
for f in "$@"; do echo "1 $f" >&2; done
""",
    )
    result = filter_dir(folder, dont_stop=True, script=script)
    assert result.stop_count == 3
    assert [step.remaining_count for step in result.steps] == [4, 3, 2]
    assert len(result.kept) == 3


def test_equal_score_is_not_a_drop_and_ends_at_two(tmp_path: Path):
    folder = tmp_path / "data"
    folder.mkdir()
    for name in ("a", "b", "c"):
        (folder / name).write_text(name)
    script = _fake(tmp_path)
    result = filter_dir(folder, script=script)
    assert result.stop_count == 2
    assert [step.remaining_count for step in result.steps] == [3, 2]


def test_tie_removes_lower_path_string(tmp_path: Path):
    files = []
    for name in ("b", "a", "c"):
        path = tmp_path / name
        path.write_text(name)
        files.append(path.resolve())
    script = _script(
        tmp_path,
        """#!/bin/sh
if [ "$1" = "--verbose" ]; then shift; fi
echo 0.5
for f in "$@"; do echo "0.2 $f" >&2; done
""",
    )
    result = filter_paths(files, dont_stop=True, script=script)
    removed_first = set(files) - set(result.steps[1].remaining)
    assert removed_first == {min(files, key=str)}


def test_path_with_space(tmp_path: Path):
    folder = tmp_path / "dir"
    folder.mkdir()
    (folder / "a b").write_text("a")
    (folder / "c").write_text("c")
    script = _script(
        tmp_path,
        """#!/bin/sh
if [ "$1" = "--verbose" ]; then shift; fi
echo 0.4
for f in "$@"; do echo "0.2 $f" >&2; done
""",
    )
    result = filter_dir(folder, script=script)
    assert result.stop_count == 2
    assert all(path.exists() for path in result.steps[0].remaining)


def test_cli_prints_kept(tmp_path: Path, monkeypatch, capsys):
    folder = tmp_path / "data"
    folder.mkdir()
    for name in ("a", "b"):
        (folder / name).write_text(name)
    script = _script(
        tmp_path,
        """#!/bin/sh
if [ "$1" = "--verbose" ]; then shift; fi
echo 0.5
for f in "$@"; do echo "0.2 $f" >&2; done
""",
    )
    monkeypatch.setattr("panhard_filter.filter._VENDORED", script)
    assert main([str(folder)]) == 0
    lines = capsys.readouterr().out.strip().splitlines()
    assert len(lines) == 2


def test_real_script_on_three_dataset_files(tmp_path: Path):
    xz = subprocess.run(["xz", "--version"], capture_output=True)
    bc = subprocess.run(["bc", "--version"], capture_output=True)
    if xz.returncode != 0 or bc.returncode != 0:
        return
    names = [
        "add_two_numbers_01.java",
        "add_two_numbers_02.java",
        "add_two_numbers_03.java",
    ]
    for name in names:
        (tmp_path / name).write_bytes((DATASET / name).read_bytes())
    result = filter_dir(tmp_path, dont_stop=True, script=REAL)
    assert [step.remaining_count for step in result.steps] == [3, 2]
    assert result.stop_count in (2, 3)
    assert len(result.kept) == result.stop_count
    assert list(tmp_path.iterdir())  # sources stay
