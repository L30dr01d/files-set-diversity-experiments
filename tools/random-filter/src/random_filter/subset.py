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


def _validate_subset(*, relative_eps: float, max_tries: int) -> None:
    if relative_eps < 0:
        raise ValueError(f"relative_eps must be >= 0, got {relative_eps}")
    if max_tries < 1:
        raise ValueError(f"max_tries must be >= 1, got {max_tries}")


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
    measure: Callable[[Path], float],
    *,
    relative_eps: float,
    max_tries: int,
    rng: Random,
    steps: list[SubsetStep],
    n_input: int,
) -> tuple[list[Path], float]:
    tmp = list(start)
    tmp_score = old
    left = 0
    right = 100
    last_removed = -1
    while left <= right:
        mid = (left + right) // 2
        num = int(len(start) * mid / 100)
        leftover = len(start) - num
        if num < 1:
            left = mid + 1
            continue
        if leftover == 0 or num == last_removed:
            right = mid - 1
            continue
        accepted = False
        for _attempt in range(max_tries):
            sample = set(rng.sample(start, num))
            remaining = [path for path in start if path not in sample]
            new = score_paths(remaining, measure)
            if old - new <= relative_eps * old:
                tmp = remaining
                tmp_score = new
                last_removed = num
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
    measure: Callable[[Path], float],
    *,
    relative_eps: float = 1e-5,
    max_tries: int = 10,
    rng: Random | None = None,
) -> SubsetResult:
    _validate_subset(relative_eps=relative_eps, max_tries=max_tries)
    current = list(files)
    if rng is None:
        rng = Random()
    if len(current) <= 1:
        return SubsetResult(kept=current, steps=[])
    n_input = len(current)
    old = score_paths(current, measure)
    steps: list[SubsetStep] = []
    _append_step(steps, n_input=n_input, score=old, remaining=current)
    while True:
        nxt, new_score = _search(
            current,
            old,
            measure,
            relative_eps=relative_eps,
            max_tries=max_tries,
            rng=rng,
            steps=steps,
            n_input=n_input,
        )
        if len(nxt) >= len(current):
            return SubsetResult(kept=current, steps=steps)
        current = nxt
        old = new_score
        if len(current) <= 1:
            return SubsetResult(kept=current, steps=steps)
