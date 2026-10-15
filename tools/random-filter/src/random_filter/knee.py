from __future__ import annotations

from pathlib import Path

from kneefinder import KneeFinder


def knee_cutoff(counts: dict[Path, int]) -> tuple[int, list[Path]]:
    input_order = list(counts.keys())
    if len(counts) < 3:
        return 0, input_order
    ordered = sorted(counts.items(), key=lambda item: item[1], reverse=True)
    paths = [path for path, _count in ordered]
    ys = [count for _path, count in ordered]
    xs = list(range(len(ys)))
    try:
        point = KneeFinder(xs, ys).find_knee()
        index = int(point[0])
    except (AssertionError, IndexError, ValueError):
        return 0, input_order
    return index, paths[index:]
