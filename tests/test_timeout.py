import importlib
import sys
import time
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

import pytest

from experiment_runner.timeout import SCORE_TIMEOUT_SECONDS, WORKER_MEMORY_BYTES
from experiment_runner.timeout import call_score, hang_score, kill_self, quick_score
from experiment_runner.timeout import call_timed, hang_reduce, raise_score


def test_timeout_constant_is_six_hours():
    assert SCORE_TIMEOUT_SECONDS == 21600


def test_worker_memory_cap_is_four_gib():
    assert WORKER_MEMORY_BYTES == 4 * 1024 * 1024 * 1024


def test_call_score_returns_float_before_timeout(tmp_path: Path):
    assert call_score(quick_score, tmp_path, timeout=5) == 0.42


def test_call_score_returns_none_on_timeout(tmp_path: Path):
    assert call_score(hang_score, tmp_path, timeout=0.5) is None


def test_unpicklable_score_runs_inline(tmp_path: Path):
    assert call_score(lambda path: 0.7, tmp_path, timeout=5) == 0.7


def test_call_timed_returns_none_on_timeout(tmp_path: Path):
    assert call_timed(hang_reduce, (tmp_path, "FAST++", 50.0), timeout=0.5) is None


def test_call_timed_returns_reduce_result(tmp_path: Path):
    def quick_reduce(_files_dir, _algo, _pct):
        return ["a.txt"]

    assert call_timed(quick_reduce, (tmp_path, "FAST-CS", 10.0), timeout=5) == ["a.txt"]


def test_call_score_returns_none_when_score_raises(tmp_path: Path, capsys):
    def boom(_path):
        raise OSError(7, "Argument list too long")

    assert call_score(boom, tmp_path, timeout=5) is None
    err = capsys.readouterr().err
    assert "warning:" in err
    assert "Argument list too long" in err


def test_call_score_returns_none_when_spawned_score_raises(tmp_path: Path, capsys):
    assert call_score(raise_score, tmp_path, timeout=5) is None
    err = capsys.readouterr().err
    assert "warning:" in err
    assert "Argument list too long" in err


def test_call_timed_returns_none_quickly_when_worker_dies(capsys):
    t0 = time.monotonic()
    assert call_timed(kill_self, (), timeout=8) is None
    assert time.monotonic() - t0 < 3
    err = capsys.readouterr().err
    assert "warning:" in err
    assert "worker exited" in err


@pytest.fixture
def memory_score(tmp_path, monkeypatch):
    monkeypatch.setattr("experiment_runner.timeout.MEMORY_SAMPLE_SECONDS", 0.05)
    module = tmp_path / "memory_score_fixture.py"
    module.write_text("""
import os
import signal
import time

def score(path):
    data = bytearray((48 if path.name == 'large' else 8) * 1024 * 1024)
    time.sleep(0.3)
    if path.name == 'timeout':
        time.sleep(10)
    if path.name == 'error':
        raise ValueError("score failed")
    if path.name == 'killed':
        os.kill(os.getpid(), signal.SIGKILL)
    return 0.42 if data[0] == 0 else 0.0
""")
    monkeypatch.syspath_prepend(str(tmp_path))
    # Each test gets its own module to avoid reusing a removed fixture directory.
    sys.modules.pop("memory_score_fixture", None)
    return importlib.import_module("memory_score_fixture").score


@pytest.mark.parametrize("mode, expected", [("large", 0.42), ("timeout", None), ("killed", None), ("error", None)])
def test_score_memory_survives_worker_exit(tmp_path, memory_score, mode, expected):
    from experiment_runner.timeout import call_score_with_memory

    value, peak = call_score_with_memory(memory_score, tmp_path / mode, timeout=1.5)
    assert value == expected
    assert peak is not None and peak >= (48 if mode == "large" else 8)


def test_score_memory_is_unavailable_for_inline_calls(tmp_path):
    from experiment_runner.timeout import call_score_with_memory

    assert call_score_with_memory(lambda _: 0.7, tmp_path) == (0.7, None)


def test_score_memory_keeps_highest_sample(tmp_path, monkeypatch):
    import experiment_runner.timeout as timing

    monkeypatch.setattr(timing, "MEMORY_SAMPLE_SECONDS", 0.05)
    samples = iter([1024**2, 3 * 1024**2, 2 * 1024**2])
    monkeypatch.setattr(timing, "_rss_bytes", lambda pid: next(samples, None))
    value, peak = timing.call_score_with_memory(hang_score, tmp_path, timeout=0.25)
    assert value is None
    assert peak == 3.0


@pytest.mark.parametrize("error_name", ["AccessDenied", "NoSuchProcess"])
def test_score_memory_access_denied_does_not_fail_score(tmp_path, memory_score, monkeypatch, error_name):
    import experiment_runner.timeout as timing
    import psutil

    def denied(self):
        raise getattr(psutil, error_name)(self.pid)

    monkeypatch.setattr(psutil.Process, "memory_info", denied)
    assert timing.call_score_with_memory(memory_score, tmp_path, timeout=5) == (0.42, None)


def test_concurrent_score_memory_is_per_worker(tmp_path, memory_score):
    from experiment_runner.timeout import call_score_with_memory

    with ThreadPoolExecutor(max_workers=2) as pool:
        futures = [pool.submit(call_score_with_memory, memory_score, tmp_path / name, timeout=5)
                   for name in ("small", "large")]
        small, large = [future.result() for future in futures]
    assert small[0] == large[0] == 0.42
    assert small[1] is not None and large[1] > small[1] + 24


def test_memory_sampling_interval_is_ten_seconds():
    from experiment_runner.timeout import MEMORY_SAMPLE_SECONDS

    assert MEMORY_SAMPLE_SECONDS == 10
