from __future__ import annotations

import subprocess
from pathlib import Path

_VENDORED = Path(__file__).resolve().parent / "panhard-xz"


def _list_files(files_dir: Path) -> list[Path]:
    if not files_dir.is_dir():
        raise ValueError(f"not a directory: {files_dir}")
    paths = sorted(
        (p.resolve() for p in files_dir.iterdir() if p.is_file()),
        key=lambda p: p.name,
    )
    if not paths:
        raise ValueError(f"no regular files in {files_dir}")
    return paths


def _run(script: Path, paths: list[Path]) -> subprocess.CompletedProcess[str]:
    result = subprocess.run(
        [str(script), "--verbose", *[str(p) for p in paths]],
        check=False,
        capture_output=True,
        text=True,
    )
    if result.returncode != 0:
        detail = result.stderr.strip() or f"exit {result.returncode}"
        raise ValueError(f"panhard-xz failed: {detail}")
    return result


def _score(result: subprocess.CompletedProcess[str]) -> float:
    try:
        return float(result.stdout.strip())
    except ValueError as exc:
        raise ValueError(f"panhard-xz score is not numeric: {result.stdout.strip()!r}") from exc


def _parse_ranking(stderr: str, paths: list[Path]) -> list[tuple[float, Path]]:
    current = {str(path): path for path in paths}
    lines = [line.strip() for line in stderr.splitlines() if line.strip()]
    if len(lines) != len(paths):
        raise ValueError(
            f"panhard-xz ranking has {len(lines)} lines, expected {len(paths)}"
        )
    ranking: list[tuple[float, Path]] = []
    seen: set[str] = set()
    for line in lines:
        parts = line.split(maxsplit=1)
        if len(parts) != 2 or parts[1] not in current or parts[1] in seen:
            raise ValueError(f"panhard-xz ranking does not name the current files: {line}")
        try:
            contribution = float(parts[0])
        except ValueError as exc:
            raise ValueError(f"panhard-xz contribution is not numeric: {parts[0]!r}") from exc
        seen.add(parts[1])
        ranking.append((contribution, current[parts[1]]))
    return ranking


def _measure(
    script: Path, paths: list[Path], *, ranked: bool
) -> tuple[float, list[tuple[float, Path]]]:
    result = _run(script, paths)
    score = _score(result)
    ranking = _parse_ranking(result.stderr, paths) if ranked else []
    return score, ranking


def _drop_least(ranking: list[tuple[float, Path]]) -> Path:
    _contribution, path = min(ranking, key=lambda item: (item[0], item[1].name))
    return path


def filter(files_dir: Path, *, script: Path | None = None) -> list[str]:
    script = script or _VENDORED
    current = _list_files(files_dir)
    if len(current) == 1:
        return [current[0].name]
    score, ranking = _measure(script, current, ranked=True)
    while len(current) > 1:
        drop = _drop_least(ranking)
        remaining = [path for path in current if path != drop]
        new_score, new_ranking = _measure(script, remaining, ranked=len(remaining) > 1)
        if new_score < score:
            return [path.name for path in current]
        current = remaining
        score = new_score
        ranking = new_ranking
    return [path.name for path in current]
