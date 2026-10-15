from pathlib import Path
from random import Random

import pytest

from random_filter.subset import filter_subset


def _files(directory: Path, count: int) -> list[Path]:
    paths = []
    for index in range(count):
        path = directory / f"f{index}.txt"
        path.write_text(f"body-{index}", encoding="utf-8")
        paths.append(path)
    return paths


def test_small_start_set_does_not_call_metric(tmp_path: Path):
    paths = _files(tmp_path, 4)

    def metric(_directory: Path) -> float:
        raise AssertionError("metric should not be called")

    result = filter_subset(paths, metric, min_keep=10)
    assert result.kept == paths
    assert result.kept is not paths
    assert result.steps == []


def test_rejects_bad_subset_arguments(tmp_path: Path):
    paths = _files(tmp_path, 1)

    def metric(_directory: Path) -> float:
        raise AssertionError("metric should not be called")

    with pytest.raises(ValueError, match="relative_eps must be >= 0"):
        filter_subset(paths, metric, relative_eps=-0.1)
    with pytest.raises(ValueError, match="max_tries must be >= 1"):
        filter_subset(paths, metric, max_tries=0)
    with pytest.raises(ValueError, match="min_keep must be >= 1"):
        filter_subset(paths, metric, min_keep=0)


def test_stages_symlinks_and_removes_the_temp_directory(tmp_path: Path):
    paths = _files(tmp_path, 4)
    seen: list[Path] = []

    def metric(directory: Path) -> float:
        seen.append(directory)
        staged = list(directory.iterdir())
        for link in staged:
            assert link.is_symlink()
            source = next(path for path in paths if path.name == link.name)
            assert link.read_bytes() == source.read_bytes()
        return 1.0 if len(staged) == len(paths) else 0.0

    filter_subset(paths, metric, min_keep=3, relative_eps=1e-5)
    assert seen
    assert all(not directory.exists() for directory in seen)
    for path in paths:
        assert path.read_text(encoding="utf-8").startswith("body-")


def test_metric_exception_still_removes_the_temp_directory(tmp_path: Path):
    paths = _files(tmp_path, 4)
    seen: list[Path] = []

    def metric(directory: Path) -> float:
        seen.append(directory)
        raise RuntimeError("boom")

    with pytest.raises(RuntimeError, match="boom"):
        filter_subset(paths, metric, min_keep=3)
    assert seen and not seen[0].exists()


def test_duplicate_names_raise_before_metric(tmp_path: Path):
    left = tmp_path / "left"
    right = tmp_path / "right"
    left.mkdir()
    right.mkdir()
    a = left / "same.txt"
    b = right / "same.txt"
    a.write_text("a", encoding="utf-8")
    b.write_text("b", encoding="utf-8")

    def metric(_directory: Path) -> float:
        raise AssertionError("metric should not be called")

    with pytest.raises(ValueError, match="duplicate file name"):
        filter_subset([a, b], metric, min_keep=1)


def test_missing_path_raises_before_metric(tmp_path: Path):
    good = tmp_path / "good.txt"
    good.write_text("ok", encoding="utf-8")

    def metric(_directory: Path) -> float:
        raise AssertionError("metric should not be called")

    with pytest.raises(ValueError, match="not a file"):
        filter_subset([good, tmp_path / "missing.txt"], metric, min_keep=1)


def test_directory_path_raises(tmp_path: Path):
    good = tmp_path / "good.txt"
    good.write_text("ok", encoding="utf-8")
    nested = tmp_path / "nested"
    nested.mkdir()

    def metric(_directory: Path) -> float:
        raise AssertionError("metric should not be called")

    with pytest.raises(ValueError, match="not a file"):
        filter_subset([good, nested], metric, min_keep=1)


def test_symlink_to_a_file_is_scored(tmp_path: Path):
    source = tmp_path / "real.txt"
    source.write_text("via-link", encoding="utf-8")
    link = tmp_path / "link.txt"
    link.symlink_to(source.resolve())
    other = tmp_path / "other.txt"
    other.write_text("other", encoding="utf-8")
    seen: list[bytes] = []

    def metric(directory: Path) -> float:
        by_name = {path.name: path.read_bytes() for path in directory.iterdir()}
        if link.name in by_name:
            seen.append(by_name[link.name])
        return 1.0 if len(by_name) == 2 else 0.0

    filter_subset([link, other], metric, min_keep=1, relative_eps=1e-5)
    assert seen[0] == b"via-link"


class _ScriptedRng:
    """Duck-typed stand-in. filter_subset only calls sample(population, k)."""

    def __init__(self, indexes: list[int]) -> None:
        self._indexes = list(indexes)

    def sample(self, population: list[Path], k: int) -> list[Path]:
        assert k == 1
        index = self._indexes.pop(0)
        return [population[index]]


def test_constant_score_removes_down_to_min_keep(tmp_path: Path):
    paths = _files(tmp_path, 6)
    sizes: list[int] = []

    def metric(directory: Path) -> float:
        size = len(list(directory.iterdir()))
        sizes.append(size)
        assert size >= 3
        return 1.0

    kept = filter_subset(paths, metric, min_keep=3, rng=Random(0)).kept
    assert len(kept) == 3
    assert [paths.index(path) for path in kept] == sorted(paths.index(path) for path in kept)
    assert min(sizes) >= 3


def test_collapsing_score_removes_nothing(tmp_path: Path):
    paths = _files(tmp_path, 6)

    def metric(directory: Path) -> float:
        size = len(list(directory.iterdir()))
        assert size >= 4
        return 1.0 if size == len(paths) else 0.0

    kept = filter_subset(paths, metric, min_keep=4, relative_eps=1e-5, rng=Random(0)).kept
    assert kept == paths


def test_small_drop_is_kept_and_large_drop_is_not(tmp_path: Path):
    paths = _files(tmp_path, 20)

    def metric(directory: Path) -> float:
        return float(len(list(directory.iterdir())))

    shrunk = filter_subset(paths, metric, min_keep=10, relative_eps=0.1, rng=Random(0)).kept
    assert len(shrunk) == 18
    assert [paths.index(path) for path in shrunk] == sorted(paths.index(path) for path in shrunk)

    held = filter_subset(paths, metric, min_keep=10, relative_eps=0.01, rng=Random(0)).kept
    assert len(held) == 20
    assert held == paths


def test_rising_score_removes_down_to_min_keep(tmp_path: Path):
    paths = _files(tmp_path, 6)

    def metric(directory: Path) -> float:
        return float(100 - len(list(directory.iterdir())))

    kept = filter_subset(paths, metric, min_keep=3, relative_eps=0.0, rng=Random(0)).kept
    assert len(kept) == 3


def test_input_list_is_not_mutated(tmp_path: Path):
    paths = _files(tmp_path, 8)
    snapshot = list(paths)
    filter_subset(paths, lambda _directory: 1.0, min_keep=3, rng=Random(0))
    assert paths == snapshot


def test_second_sample_can_accept_after_the_first_fails(tmp_path: Path):
    paths = _files(tmp_path, 3)

    def metric(directory: Path) -> float:
        names = {path.name for path in directory.iterdir()}
        return 0.0 if paths[0].name not in names else 1.0

    held = filter_subset(
        paths,
        metric,
        min_keep=2,
        max_tries=1,
        relative_eps=0.0,
        rng=_ScriptedRng([0]),
    ).kept
    assert held == paths

    kept = filter_subset(
        paths,
        metric,
        min_keep=2,
        max_tries=2,
        relative_eps=0.0,
        rng=_ScriptedRng([0, 1]),
    ).kept
    assert kept == [paths[0], paths[2]]


def test_step_zero_is_the_initial_score_at_100_percent(tmp_path: Path):
    paths = _files(tmp_path, 6)

    def metric(directory: Path) -> float:
        return 1.0 if len(list(directory.iterdir())) == 6 else 0.0

    result = filter_subset(paths, metric, min_keep=4, relative_eps=1e-5, rng=Random(0))
    assert result.kept == paths
    assert len(result.steps) == 1
    step = result.steps[0]
    assert step.index == 0
    assert step.score == 1.0
    assert step.remaining_count == 6
    assert step.remaining_pct == 100.0


def test_committed_shrink_appends_a_step_against_original_n(tmp_path: Path):
    paths = _files(tmp_path, 20)

    def metric(directory: Path) -> float:
        return float(len(list(directory.iterdir())))

    result = filter_subset(paths, metric, min_keep=10, relative_eps=0.1, rng=Random(0))
    assert len(result.kept) == 18
    assert [step.index for step in result.steps] == list(range(len(result.steps)))
    assert result.steps[0].remaining_count == 20
    assert result.steps[0].remaining_pct == 100.0
    assert result.steps[0].score == 20.0
    assert result.steps[-1].remaining_count == 18
    assert result.steps[-1].remaining_pct == 90.0
    assert result.steps[-1].score == 18.0
    assert result.steps[-1].remaining_count == len(result.kept)
    counts = [step.remaining_count for step in result.steps]
    assert counts == sorted(counts, reverse=True)
    assert len(set(counts)) == len(counts)


def test_constant_score_records_each_committed_shrink(tmp_path: Path):
    paths = _files(tmp_path, 6)

    def metric(_directory: Path) -> float:
        return 1.0

    result = filter_subset(paths, metric, min_keep=3, rng=Random(0))
    assert len(result.kept) == 3
    assert result.steps[0].index == 0
    assert result.steps[0].score == 1.0
    assert result.steps[0].remaining_count == 6
    assert result.steps[0].remaining_pct == 100.0
    assert result.steps[-1].remaining_count == 3
    assert result.steps[-1].remaining_pct == 50.0
    assert len(result.steps) >= 2
    counts = [step.remaining_count for step in result.steps]
    assert counts == sorted(counts, reverse=True)
    assert len(set(counts)) == len(counts)


def test_constant_score_records_each_accepted_probe(tmp_path: Path):
    paths = _files(tmp_path, 100)

    def metric(_directory: Path) -> float:
        return 1.0

    result = filter_subset(paths, metric, min_keep=10, rng=Random(0))
    counts = [step.remaining_count for step in result.steps]
    assert counts[0] == 100
    assert result.steps[0].remaining_pct == 100.0
    assert 50 in counts
    assert 25 in counts
    assert counts == sorted(counts, reverse=True)
    assert len(set(counts)) == len(counts)
    assert [step.index for step in result.steps] == list(range(len(result.steps)))
    assert result.steps[-1].remaining_count == len(result.kept)
    assert result.steps[-1].remaining_pct == 100.0 * len(result.kept) / 100
