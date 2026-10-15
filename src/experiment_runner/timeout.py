from __future__ import annotations

import importlib.machinery
import multiprocessing
import pickle
import sys
import time
from collections.abc import Callable
from pathlib import Path

SCORE_TIMEOUT_SECONDS = 20 * 60

ScoreFn = Callable[[Path], float]


def hang_score(_files_dir: Path) -> float:
    time.sleep(10_000)
    return 0.0


def hang_reduce(_files_dir: Path, _algo: str, _pct: float) -> list[str]:
    time.sleep(10_000)
    return ["x"]


def raise_score(_files_dir: Path) -> float:
    raise OSError(7, "Argument list too long")


def quick_score(_files_dir: Path) -> float:
    return 0.42


def _invoke(fn: Callable, args: tuple):
    return fn(*args)


def _score_worker(score_fn: ScoreFn, path: str) -> float:
    return float(score_fn(Path(path)))


def _can_spawn(fn: Callable, args: tuple) -> bool:
    try:
        pickle.dumps((fn, args))
    except Exception:
        return False
    name = getattr(fn, "__module__", "") or ""
    if not name or name == "__main__":
        return True
    top = name.split(".", 1)[0]
    try:
        return importlib.machinery.PathFinder.find_spec(top) is not None
    except (ImportError, ModuleNotFoundError, ValueError):
        return False


def call_timed(
    fn: Callable,
    args: tuple,
    *,
    timeout: float = SCORE_TIMEOUT_SECONDS,
):
    if not _can_spawn(fn, args):
        try:
            return fn(*args)
        except Exception as exc:  # noqa: BLE001
            print(f"warning: {exc}", file=sys.stderr)
            return None
    ctx = multiprocessing.get_context("spawn")
    pool = ctx.Pool(1)
    try:
        result = pool.apply_async(_invoke, (fn, args))
        try:
            return result.get(timeout=timeout)
        except multiprocessing.TimeoutError:
            return None
        except Exception as exc:  # noqa: BLE001
            print(f"warning: {exc}", file=sys.stderr)
            return None
    finally:
        pool.terminate()
        pool.join()


def call_score(
    score_fn: ScoreFn,
    files_dir: Path,
    *,
    timeout: float = SCORE_TIMEOUT_SECONDS,
) -> float | None:
    value = call_timed(_score_worker, (score_fn, str(files_dir)), timeout=timeout)
    if value is None:
        return None
    return float(value)
