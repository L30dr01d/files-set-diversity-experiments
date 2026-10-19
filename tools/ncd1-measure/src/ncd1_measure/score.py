from __future__ import annotations

import lzma
from pathlib import Path


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


def _c_of_concat(parts: list[bytes]) -> int:
    if not parts:
        return 0
    return len(lzma.compress(b"".join(parts)))


def score(files_dir: Path) -> float:
    paths = _list_files(files_dir)
    if len(paths) < 3:
        return 0.0
    members = [p.read_bytes() for p in paths]
    c_full = _c_of_concat(members)
    min_c_single = min(len(lzma.compress(m)) for m in members)
    c_without = [
        _c_of_concat([b for i, b in enumerate(members) if i != skip])
        for skip in range(len(members))
    ]
    max_residual = max(c_without)
    if max_residual <= 0:
        return 0.0
    return float((c_full - min_c_single) / max_residual)
