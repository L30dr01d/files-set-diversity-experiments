from __future__ import annotations

from pathlib import Path

from levassor_metric.hll import HyperLogLog
from levassor_metric.shingles import file_shingles


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


def score(files_dir: Path) -> float:
    paths = _list_files(files_dir)
    if len(paths) < 3:
        raise ValueError(f"levassor_metric requires >= 3 files, got {len(paths)}")
    denom = 0
    sketch = HyperLogLog(p=14)
    for path in paths:
        hashes = file_shingles(path.read_bytes())
        denom += len(hashes)
        for hashed in hashes:
            sketch.add(hashed)
    if denom == 0:
        return 0.0
    value = sketch.cardinality() / denom
    return float(min(1.0, max(0.0, value)))
