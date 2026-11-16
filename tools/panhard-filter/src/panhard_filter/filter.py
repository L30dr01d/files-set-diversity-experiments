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
    residual: float


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


def rank_set(
    paths: Sequence[Path], *, script: Path, ranking: str
) -> tuple[float, float, list[tuple[float, Path]]]:
    if ranking not in ("dpi", "rni"):
        raise ValueError(f"unknown Panhard ranking method: {ranking}")
    result = subprocess.run(
        [str(script), "--verbose", *[str(p) for p in paths]],
        check=True,
        capture_output=True,
        text=True,
    )
    score = float(result.stdout.strip())
    ranked: list[tuple[float, Path]] = []
    residual = None
    for line in result.stderr.splitlines():
        if not line.strip():
            continue
        if line.startswith("residual "):
            residual = float(line.split(maxsplit=1)[1])
            continue
        dpi_label, dpi, rni_label, rni, raw_path = line.split(maxsplit=4)
        if (dpi_label, rni_label) != ("dpi", "rni"):
            raise ValueError(f"unexpected panhard-xz output: {line}")
        ranked.append((float(dpi if ranking == "dpi" else rni), Path(raw_path)))
    if len(ranked) != len(paths):
        raise RuntimeError(
            f"panhard-xz ranked {len(ranked)} files, expected {len(paths)}"
        )
    if residual is None:
        raise RuntimeError("panhard-xz did not report a residual")
    return score, residual, ranked


def _least_important(ranking: Sequence[tuple[float, Path]]) -> Path:
    return min(ranking, key=lambda item: (item[0], str(item[1])))[1]


def filter_paths(
    paths: Sequence[Path],
    *,
    ranking: str,
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
        score, residual, ranked = rank_set(current, script=script, ranking=ranking)
        remaining = tuple(current)
        steps.append(
            FilterStep(len(remaining), score, remaining, residual)
        )
        if previous is not None and score < previous and stop_count is None:
            stop_count = len(remaining)
            if not dont_stop:
                break
        if len(current) <= 2:
            break
        victim = _least_important(ranked).resolve()
        nxt = [path for path in current if path.resolve() != victim]
        if len(nxt) != len(current) - 1:
            raise RuntimeError(f"ranked file not in the set: {victim}")
        current = nxt
        previous = score
    if stop_count is None:
        stop_count = steps[-1].remaining_count
    kept = next(step.remaining for step in steps if step.remaining_count == stop_count)
    return FilterResult(kept=list(kept), steps=steps, stop_count=stop_count)


def filter_dir(
    files_dir: Path,
    *,
    ranking: str,
    dont_stop: bool = False,
    script: Path | None = None,
) -> FilterResult:
    return filter_paths(
        _list_files(files_dir), ranking=ranking, dont_stop=dont_stop, script=script
    )
