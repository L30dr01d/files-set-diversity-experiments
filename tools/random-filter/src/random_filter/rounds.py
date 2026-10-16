from __future__ import annotations

from collections.abc import Callable, Sequence
from concurrent.futures import ThreadPoolExecutor
from dataclasses import dataclass
from pathlib import Path
from random import Random

from random_filter.knee import knee_cutoff
from random_filter.stop import should_stop
from random_filter.subset import filter_subset


@dataclass(frozen=True)
class FilterResult:
    kept: list[Path]
    removal_counts: dict[Path, int]
    knees: list[int]
    rounds_finished: int


def _validate_rounds(
    *,
    rounds: int,
    split_by: int,
    relative_eps: float,
    max_tries: int,
    min_keep: int,
    stop_pct: float | None,
    min_stop_rounds: int,
    workers: int,
) -> None:
    if rounds < 1:
        raise ValueError(f"rounds must be >= 1, got {rounds}")
    if split_by < 1:
        raise ValueError(f"split_by must be >= 1, got {split_by}")
    if relative_eps < 0:
        raise ValueError(f"relative_eps must be >= 0, got {relative_eps}")
    if max_tries < 1:
        raise ValueError(f"max_tries must be >= 1, got {max_tries}")
    if min_keep < 1:
        raise ValueError(f"min_keep must be >= 1, got {min_keep}")
    if min_stop_rounds < 1:
        raise ValueError(f"min_stop_rounds must be >= 1, got {min_stop_rounds}")
    if workers < 1:
        raise ValueError(f"workers must be >= 1, got {workers}")
    if stop_pct is not None and stop_pct < 0:
        raise ValueError(f"stop_pct must be >= 0, got {stop_pct}")


def _chunks_in_input_order(files: Sequence[Path], order: list[Path], split_by: int) -> list[list[Path]]:
    position = {path: index for index, path in enumerate(files)}
    raw = [order[index : index + split_by] for index in range(0, len(order), split_by)]
    return [sorted(chunk, key=lambda path: position[path]) for chunk in raw]


def filter_rounds(
    files: Sequence[Path],
    measure: Callable[[Path], float],
    *,
    rounds: int,
    split_by: int = 50,
    relative_eps: float = 1e-5,
    max_tries: int = 10,
    min_keep: int = 10,
    stop_pct: float | None = 0.03,
    min_stop_rounds: int = 20,
    workers: int = 1,
    rng: Random | None = None,
) -> FilterResult:
    _validate_rounds(
        rounds=rounds,
        split_by=split_by,
        relative_eps=relative_eps,
        max_tries=max_tries,
        min_keep=min_keep,
        stop_pct=stop_pct,
        min_stop_rounds=min_stop_rounds,
        workers=workers,
    )
    if len(files) == 0:
        return FilterResult(kept=[], removal_counts={}, knees=[], rounds_finished=0)
    if rng is None:
        rng = Random()
    counts = {path: 0 for path in files}
    knees: list[int] = []
    finished = 0
    for _round in range(rounds):
        round_rng = Random(rng.randrange(2**32))
        order = list(files)
        round_rng.shuffle(order)
        chunks = _chunks_in_input_order(files, order, split_by)
        seeds = [round_rng.randrange(2**32) for _chunk in chunks]
        with ThreadPoolExecutor(max_workers=workers) as pool:
            futures = [
                pool.submit(
                    filter_subset,
                    chunk,
                    measure,
                    relative_eps=relative_eps,
                    max_tries=max_tries,
                    min_keep=min_keep,
                    rng=Random(seed),
                )
                for chunk, seed in zip(chunks, seeds)
            ]
            kept_per_chunk = [future.result().kept for future in futures]
        for chunk, kept in zip(chunks, kept_per_chunk):
            kept_set = set(kept)
            for path in chunk:
                if path not in kept_set:
                    counts[path] += 1
        _index, _kept = knee_cutoff(counts)
        knees.append(_index)
        finished += 1
        if should_stop(
            knees,
            file_count=len(files),
            stop_pct=stop_pct,
            min_stop_rounds=min_stop_rounds,
        ):
            break
    _index, kept = knee_cutoff(counts)
    return FilterResult(
        kept=kept,
        removal_counts=counts,
        knees=knees,
        rounds_finished=finished,
    )
