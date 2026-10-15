from __future__ import annotations

import lzma
from concurrent.futures import as_completed, ThreadPoolExecutor
from pathlib import Path

from poisson_metric.value import poisson_metric_value


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


def _ncd(x_len: int, y_len: int, xy_len: int) -> float:
    return (xy_len - min(x_len, y_len)) / max(x_len, y_len)


def _pair_distance(
    i: int,
    j: int,
    texts: list[str],
    caches: list[int],
) -> tuple[tuple[int, int], float]:
    xy = len(lzma.compress((texts[i] + texts[j]).encode("utf-8")))
    return ((i, j), _ncd(caches[i], caches[j], xy))


def score(files_dir: Path, max_workers: int = 10) -> float:
    paths = _list_files(files_dir)
    texts = [p.read_text(encoding="utf-8", errors="replace") for p in paths]
    caches = [len(lzma.compress(t.encode("utf-8"))) for t in texts]
    n = len(texts)
    distances: dict[tuple[int, int], float] = {}
    with ThreadPoolExecutor(max_workers=max_workers) as pool:
        futures = [
            pool.submit(_pair_distance, i, j, texts, caches)
            for i in range(n)
            for j in range(i, n)
        ]
        for fut in as_completed(futures):
            key, value = fut.result()
            distances[key] = value
    return poisson_metric_value(distances)
