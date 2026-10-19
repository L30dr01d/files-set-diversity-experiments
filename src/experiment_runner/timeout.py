from __future__ import annotations

import importlib.machinery
import multiprocessing
import pickle
import sys
import time
from collections.abc import Callable
from pathlib import Path

SCORE_TIMEOUT_SECONDS = 60 * 60
WORKER_MEMORY_BYTES = 4 * 1024 * 1024 * 1024

ScoreFn = Callable[[Path], float]


def hang_score(_files_dir: Path) -> float:
    time.sleep(10_000)
    return 0.0


def hang_reduce(_files_dir: Path, _algo: str, _pct: float) -> list[str]:
    time.sleep(10_000)
    return ["x"]


def hang_filter(paths, measure, *, relative_eps, max_tries, min_keep, rng):
    time.sleep(10_000)
    return None


def raise_score(_files_dir: Path) -> float:
    raise OSError(7, "Argument list too long")


def quick_score(_files_dir: Path) -> float:
    return 0.42


def kill_self(*_args) -> float:
    import os
    import signal

    os.kill(os.getpid(), signal.SIGKILL)
    return 0.0


def _score_worker(score_fn: ScoreFn, path: str) -> float:
    return float(score_fn(Path(path)))


def _apply_memory_cap(max_bytes: int | None) -> None:
    if max_bytes is None:
        return
    try:
        import resource
    except ImportError:
        return
    try:
        resource.setrlimit(resource.RLIMIT_AS, (max_bytes, max_bytes))
    except (ValueError, OSError):
        return


def _run_worker(fn: Callable, args: tuple, conn, memory_bytes: int | None) -> None:
    _apply_memory_cap(memory_bytes)
    try:
        conn.send(("ok", fn(*args)))
    except Exception as exc:  # noqa: BLE001
        try:
            conn.send(("err", f"{type(exc).__name__}: {exc}"))
        except Exception:  # noqa: BLE001
            pass
    finally:
        conn.close()


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
    memory_bytes: int | None = WORKER_MEMORY_BYTES,
):
    if not _can_spawn(fn, args):
        try:
            return fn(*args)
        except Exception as exc:  # noqa: BLE001
            print(f"warning: {exc}", file=sys.stderr)
            return None
    ctx = multiprocessing.get_context("spawn")
    parent_conn, child_conn = ctx.Pipe(duplex=False)
    proc = ctx.Process(
        target=_run_worker,
        args=(fn, args, child_conn, memory_bytes),
    )
    proc.start()
    child_conn.close()
    try:
        proc.join(timeout)
        if proc.is_alive():
            proc.kill()
            proc.join()
            return None
        if proc.exitcode not in (0, None):
            print(f"warning: worker exited with code {proc.exitcode}", file=sys.stderr)
            return None
        if not parent_conn.poll():
            return None
        status, payload = parent_conn.recv()
        if status == "ok":
            return payload
        print(f"warning: {payload}", file=sys.stderr)
        return None
    finally:
        parent_conn.close()
        if proc.is_alive():
            proc.kill()
            proc.join()


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
