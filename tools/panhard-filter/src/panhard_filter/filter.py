from __future__ import annotations

import subprocess
from collections.abc import Sequence
from dataclasses import dataclass
from pathlib import Path

_VENDORED = Path(__file__).resolve().parent / "panhard-xz"


@dataclass(frozen=True)
class FilterStep:
    remaining_count: int
    score: float
    remaining: tuple[Path, ...]


@dataclass(frozen=True)
class FilterResult:
    kept: list[Path]
    steps: list[FilterStep]
    stop_count: int


def _list_files(files_dir: Path) -> list[Path]:
    if not files_dir.is_dir():
        raise ValueError(f"not a directory: {files_dir}")
    paths = sorted(
        (p for p in files_dir.iterdir() if p.is_file()),
        key=lambda p: p.name,
    )
    if len(paths) < 2:
        raise ValueError(f"need at least 2 regular files in {files_dir}")
    return paths


def rank_set(paths: Sequence[Path], *, script: Path) -> tuple[float, list[tuple[float, Path]]]:
    result = subprocess.run(
        [str(script), "--verbose", *[str(p) for p in paths]],
        check=True,
        capture_output=True,
        text=True,
    )
    score = float(result.stdout.strip())
    ranking: list[tuple[float, Path]] = []
    for line in result.stderr.splitlines():
        if not line.strip():
            continue
        value, raw_path = line.split(maxsplit=1)
        ranking.append((float(value), Path(raw_path)))
    if len(ranking) != len(paths):
        raise RuntimeError(
            f"panhard-xz ranked {len(ranking)} files, expected {len(paths)}"
        )
    return score, ranking


def _least_important(ranking: Sequence[tuple[float, Path]]) -> Path:
    return min(ranking, key=lambda item: (item[0], str(item[1])))[1]


def filter_paths(
    paths: Sequence[Path],
    *,
    dont_stop: bool = False,
    script: Path | None = None,
) -> FilterResult:
    script = script or _VENDORED
    current = [path.resolve() for path in paths]
    if len(current) < 2:
        raise ValueError("need at least 2 files")
    steps: list[FilterStep] = []
    stop_count: int | None = None
    previous: float | None = None
    while True:
        score, ranking = rank_set(current, script=script)
        remaining = tuple(current)
        steps.append(
            FilterStep(remaining_count=len(remaining), score=score, remaining=remaining)
        )
        if previous is not None and score < previous and stop_count is None:
            stop_count = len(remaining)
            if not dont_stop:
                break
        if len(current) <= 2:
            break
        victim = _least_important(ranking).resolve()
        nxt = [path for path in current if path.resolve() != victim]
        if len(nxt) != len(current) - 1:
            raise RuntimeError(f"ranked file not in the set: {victim}")
        current = nxt
        previous = score
    if stop_count is None:
        stop_count = steps[-1].remaining_count
    kept = next(step.remaining for step in steps if step.remaining_count == stop_count)
    return FilterResult(kept=list(kept), steps=steps, stop_count=stop_count)


def filter_dir(files_dir: Path, *, dont_stop: bool = False, script: Path | None = None) -> FilterResult:
    return filter_paths(_list_files(files_dir), dont_stop=dont_stop, script=script)
