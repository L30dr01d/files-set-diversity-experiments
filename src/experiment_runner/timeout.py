from __future__ import annotations

import multiprocessing
import pickle
import time
from collections.abc import Callable
from pathlib import Path

SCORE_TIMEOUT_SECONDS = 20 * 60

ScoreFn = Callable[[Path], float]


def hang_score(_files_dir: Path) -> float:
    time.sleep(10_000)
    return 0.0


def quick_score(_files_dir: Path) -> float:
    return 0.42


def _invoke(score_fn: ScoreFn, path: str) -> float:
    return float(score_fn(Path(path)))


def call_score(
    score_fn: ScoreFn,
    files_dir: Path,
    *,
    timeout: float = SCORE_TIMEOUT_SECONDS,
) -> float | None:
    try:
        pickle.dumps(score_fn)
    except Exception:
        return float(score_fn(files_dir))
    ctx = multiprocessing.get_context("spawn")
    pool = ctx.Pool(1)
    try:
        result = pool.apply_async(_invoke, (score_fn, str(files_dir)))
        try:
            return float(result.get(timeout=timeout))
        except multiprocessing.TimeoutError:
            pool.terminate()
            return None
    finally:
        pool.close()
        pool.join()
