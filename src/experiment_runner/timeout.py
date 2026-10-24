from __future__ import annotations

import importlib.machinery
import multiprocessing
import pickle
import sys
import time
from collections.abc import Callable
from pathlib import Path

SCORE_TIMEOUT_SECONDS = 21600
MEMORY_SAMPLE_SECONDS = 10
WORKER_MEMORY_BYTES = 4 * 1024 * 1024 * 1024

ScoreFn = Callable[[Path], float]


def hang_score(_files_dir: Path) -> float:
    time.sleep(10_000)
    return 0.0


def hang_reduce(_files_dir: Path, _algo: str, _pct: float) -> list[str]:
    time.sleep(10_000)
    return ["x"]


def hang_filter(paths, measure, *, relative_eps, max_tries, rng):
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


def _rss_bytes(pid: int) -> int | None:
    import psutil

    try:
        return psutil.Process(pid).memory_info().rss
    except (psutil.Error, OSError):
        return None


def _call_timed(
    fn: Callable,
    args: tuple,
    *,
    timeout: float,
    memory_bytes: int | None,
    measure_memory: bool = False,
) -> tuple[object, float | None]:
    if not _can_spawn(fn, args):
        try:
            return fn(*args), None
        except Exception as exc:  # noqa: BLE001
            print(f"warning: {exc}", file=sys.stderr)
            return None, None
    ctx = multiprocessing.get_context("spawn")
    parent_conn, child_conn = ctx.Pipe(duplex=False)
    proc = ctx.Process(
        target=_run_worker,
        args=(fn, args, child_conn, memory_bytes),
    )
    peak_bytes = None
    proc.start()
    child_conn.close()
    try:
        deadline = time.monotonic() + timeout
        while proc.is_alive():
            if measure_memory:
                rss = _rss_bytes(proc.pid)
                if rss is not None:
                    peak_bytes = max(peak_bytes or 0, rss)
            remaining = deadline - time.monotonic()
            if remaining <= 0:
                proc.kill()
                proc.join()
                return None, None if peak_bytes is None else peak_bytes / 1024**2
            # shortcut: sampling can miss brief spikes; use OS accounting if exact peaks are required.
            proc.join(min(MEMORY_SAMPLE_SECONDS, remaining) if measure_memory else remaining)
        peak_mib = None if peak_bytes is None else peak_bytes / 1024**2
        if proc.exitcode not in (0, None):
            print(f"warning: worker exited with code {proc.exitcode}", file=sys.stderr)
            return None, peak_mib
        if not parent_conn.poll():
            return None, peak_mib
        status, payload = parent_conn.recv()
        if status == "ok":
            return payload, peak_mib
        print(f"warning: {payload}", file=sys.stderr)
        return None, peak_mib
    finally:
        parent_conn.close()
        if proc.is_alive():
            proc.kill()
            proc.join()
        proc.close()


def call_timed(
    fn: Callable,
    args: tuple,
    *,
    timeout: float = SCORE_TIMEOUT_SECONDS,
    memory_bytes: int | None = WORKER_MEMORY_BYTES,
):
    value, _peak = _call_timed(fn, args, timeout=timeout, memory_bytes=memory_bytes)
    return value


def call_score_with_memory(
    score_fn: ScoreFn,
    files_dir: Path,
    *,
    timeout: float = SCORE_TIMEOUT_SECONDS,
) -> tuple[float | None, float | None]:
    value, peak = _call_timed(
        _score_worker, (score_fn, str(files_dir)), timeout=timeout,
        memory_bytes=WORKER_MEMORY_BYTES, measure_memory=True,
    )
    return (None if value is None else float(value)), peak


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
