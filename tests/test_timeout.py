from pathlib import Path

from experiment_runner.timeout import SCORE_TIMEOUT_SECONDS, call_score, hang_score, quick_score


def test_timeout_constant_is_twenty_minutes():
    assert SCORE_TIMEOUT_SECONDS == 20 * 60


def test_call_score_returns_float_before_timeout(tmp_path: Path):
    assert call_score(quick_score, tmp_path, timeout=5) == 0.42


def test_call_score_returns_none_on_timeout(tmp_path: Path):
    assert call_score(hang_score, tmp_path, timeout=0.5) is None


def test_unpicklable_score_runs_inline(tmp_path: Path):
    assert call_score(lambda path: 0.7, tmp_path, timeout=5) == 0.7
