from __future__ import annotations

from matplotlib.cbook import boxplot_stats


def should_stop(
    knees: list[int],
    *,
    file_count: int,
    stop_pct: float | None,
    min_stop_rounds: int,
) -> bool:
    if stop_pct is None:
        return False
    if len(knees) < min_stop_rounds:
        return False
    stat = boxplot_stats(knees)[0]
    eps = file_count * stop_pct
    q1 = float(stat["q1"])
    med = float(stat["med"])
    q3 = float(stat["q3"])
    return q1 + eps > med > q3 - eps
