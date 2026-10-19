import time
from pathlib import Path

from experiment_runner.timeout import SCORE_TIMEOUT_SECONDS, WORKER_MEMORY_BYTES
from experiment_runner.timeout import call_score, hang_score, kill_self, quick_score
from experiment_runner.timeout import call_timed, hang_reduce, raise_score


def test_timeout_constant_is_one_hour():
    assert SCORE_TIMEOUT_SECONDS == 60 * 60


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
