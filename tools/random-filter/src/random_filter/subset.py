from __future__ import annotations

from collections.abc import Callable, Sequence
from dataclasses import dataclass
from pathlib import Path
from random import Random

from random_filter.stage import score_paths


@dataclass(frozen=True)
class SubsetStep:
    index: int
    score: float
    remaining_count: int
    remaining_pct: float
    remaining: tuple[Path, ...]


@dataclass(frozen=True)
class SubsetResult:
    kept: list[Path]
    steps: list[SubsetStep]


def _validate_subset(*, relative_eps: float, max_tries: int, min_keep: int) -> None:
    if relative_eps < 0:
        raise ValueError(f"relative_eps must be >= 0, got {relative_eps}")
    if max_tries < 1:
        raise ValueError(f"max_tries must be >= 1, got {max_tries}")
    if min_keep < 1:
        raise ValueError(f"min_keep must be >= 1, got {min_keep}")


def _append_step(
    steps: list[SubsetStep],
    *,
    n_input: int,
    score: float,
    remaining: Sequence[Path],
) -> None:
    remaining_tuple = tuple(remaining)
    steps.append(
        SubsetStep(
            index=len(steps),
            score=score,
            remaining_count=len(remaining_tuple),
            remaining_pct=100.0 * len(remaining_tuple) / n_input,
            remaining=remaining_tuple,
        )
    )


def _search(
    start: list[Path],
    old: float,
    metric: Callable[[Path], float],
    *,
    relative_eps: float,
    max_tries: int,
    min_keep: int,
    rng: Random,
    last_removed: list[int],
    steps: list[SubsetStep],
    n_input: int,
) -> tuple[list[Path], float]:
    tmp = list(start)
    tmp_score = old
    left = 0
    right = 100
    while left <= right:
        mid = (left + right) // 2
        pct = mid / 100
        num = int(len(start) * pct)
        if (
            num < 1
            or pct == 1.0
            or len(start) - num < min_keep
            or num == last_removed[0]
        ):
            return tmp, tmp_score
        accepted = False
        for _attempt in range(max_tries):
            sample = set(rng.sample(start, num))
            remaining = [path for path in start if path not in sample]
            new = score_paths(remaining, metric)
            if old - new <= relative_eps * old:
                tmp = remaining
                tmp_score = new
                last_removed[0] = num
                accepted = True
                _append_step(
                    steps,
                    n_input=n_input,
                    score=new,
                    remaining=remaining,
                )
                break
        if accepted:
            left = mid + 1
        else:
            right = mid - 1
    return tmp, tmp_score


def filter_subset(
    files: Sequence[Path],
    metric: Callable[[Path], float],
    *,
    relative_eps: float = 1e-5,
    max_tries: int = 10,
    min_keep: int = 10,
    rng: Random | None = None,
) -> SubsetResult:
    _validate_subset(relative_eps=relative_eps, max_tries=max_tries, min_keep=min_keep)
    current = list(files)
    if rng is None:
        rng = Random()
    if len(current) <= min_keep:
        return SubsetResult(kept=current, steps=[])
    n_input = len(current)
    old = score_paths(current, metric)
    steps: list[SubsetStep] = []
    _append_step(steps, n_input=n_input, score=old, remaining=current)
    last_removed = [-1]
    while True:
        nxt, new_score = _search(
            current,
            old,
            metric,
            relative_eps=relative_eps,
            max_tries=max_tries,
            min_keep=min_keep,
            rng=rng,
            last_removed=last_removed,
            steps=steps,
            n_input=n_input,
        )
        if len(nxt) >= len(current):
            return SubsetResult(kept=current, steps=steps)
        current = nxt
        old = new_score
        if len(current) <= min_keep:
            return SubsetResult(kept=current, steps=steps)
