from __future__ import annotations

import subprocess
from pathlib import Path

_VENDORED = Path(__file__).resolve().parent / "panhard-xz"


def _list_files(files_dir: Path) -> list[Path]:
    if not files_dir.is_dir():
        raise ValueError(f"not a directory: {files_dir}")
    paths = sorted(
        (p for p in files_dir.iterdir() if p.is_file()),
        key=lambda p: p.name,
    )
    if not paths:
        raise ValueError(f"no regular files in {files_dir}")
    return paths


def score(files_dir: Path, *, script: Path | None = None) -> float:
    script = script or _VENDORED
    paths = _list_files(files_dir)
    result = subprocess.run(
        [str(script), *[str(p) for p in paths]],
        check=True,
        capture_output=True,
        text=True,
    )
    return float(result.stdout.strip())
