import inspect
from pathlib import Path
from random import Random

import pytest

from random_filter import FilterResult, filter_rounds
from random_filter import __all__ as exported
from random_filter.rounds import _chunks_in_input_order


def _files(directory: Path, count: int) -> list[Path]:
    paths = []
    for index in range(count):
        path = directory / f"f{index}.txt"
        path.write_text(f"body-{index}", encoding="utf-8")
        paths.append(path)
    return paths


def test_exports_are_only_the_public_names():
    assert set(exported) == {
        "filter_subset",
        "filter_rounds",
        "FilterResult",
        "SubsetResult",
        "SubsetStep",
    }


def test_chunks_restore_input_order():
    files = [Path(str(index)) for index in range(5)]
    shuffled = [files[3], files[1], files[4], files[0], files[2]]
    chunks = _chunks_in_input_order(files, shuffled, 3)
    assert chunks[0] == [files[1], files[3], files[4]]
    assert chunks[1] == [files[0], files[2]]


def test_empty_input_skips_the_measure():
    def measure(_directory: Path) -> float:
        raise AssertionError("measure should not be called")

    result = filter_rounds([], measure, rounds=1)
    assert result == FilterResult(kept=[], removal_counts={}, knees=[], rounds_finished=0)


def test_empty_input_still_validates_rounds():
    with pytest.raises(ValueError, match="rounds must be >= 1"):
        filter_rounds([], lambda _directory: 1.0, rounds=0)


@pytest.mark.parametrize(
    ("kwargs", "match"),
    [
        ({"rounds": 0}, "rounds must be >= 1"),
        ({"split_by": 0}, "split_by must be >= 1"),
        ({"max_tries": 0}, "max_tries must be >= 1"),
        ({"workers": 0}, "workers must be >= 1"),
        ({"min_stop_rounds": 0}, "min_stop_rounds must be >= 1"),
        ({"relative_eps": -0.1}, "relative_eps must be >= 0"),
        ({"stop_pct": -0.1}, "stop_pct must be >= 0"),
    ],
)
def test_invalid_arguments_do_not_call_measure(tmp_path: Path, kwargs: dict, match: str):
    paths = _files(tmp_path, 1)

    def measure(_directory: Path) -> float:
        raise AssertionError("measure should not be called")

    with pytest.raises(ValueError, match=match):
        filter_rounds(paths, measure, **{"rounds": 1, **kwargs})


def test_same_seed_is_repeatable(tmp_path: Path):
    paths = _files(tmp_path, 9)

    def measure(directory: Path) -> float:
        return float(len(list(directory.iterdir())))

    kwargs = dict(
        rounds=3,
        split_by=4,
        relative_eps=0.2,
        stop_pct=None,
        rng=Random(1),
    )
    first = filter_rounds(paths, measure, **kwargs)
    kwargs["rng"] = Random(1)
    second = filter_rounds(paths, measure, **kwargs)
    assert first == second
    assert list(first.removal_counts) == paths


def test_workers_match_the_single_thread_result(tmp_path: Path):
    paths = _files(tmp_path, 9)

    def measure(directory: Path) -> float:
        return float(len(list(directory.iterdir())))

    common = dict(
        rounds=2,
        split_by=3,
        relative_eps=0.2,
        stop_pct=None,
    )
    one = filter_rounds(paths, measure, workers=1, rng=Random(2), **common)
    two = filter_rounds(paths, measure, workers=2, rng=Random(2), **common)
    assert one == two


def test_stop_pct_none_runs_every_round(tmp_path: Path):
    paths = _files(tmp_path, 6)

    def measure(_directory: Path) -> float:
        return 1.0

    result = filter_rounds(
        paths,
        measure,
        rounds=4,
        split_by=2,
        stop_pct=None,
        rng=Random(0),
    )
    assert result.rounds_finished == 4
    assert result.knees == [2, 2, 2, 2]


def test_stable_knee_stops_after_min_stop_rounds(tmp_path: Path):
    paths = _files(tmp_path, 6)
    snapshot = list(paths)

    def measure(_directory: Path) -> float:
        return 1.0

    result = filter_rounds(
        paths,
        measure,
        rounds=30,
        split_by=2,
        stop_pct=0.03,
        min_stop_rounds=5,
        rng=Random(0),
    )
    assert result.rounds_finished == 5
    assert result.knees == [2, 2, 2, 2, 0]
    assert set(result.kept) == set(paths)
    assert paths == snapshot
    for path in paths:
        assert path.read_text(encoding="utf-8").startswith("body-")


def test_duplicate_names_inside_one_chunk_raise(tmp_path: Path):
    left = tmp_path / "left"
    right = tmp_path / "right"
    left.mkdir()
    right.mkdir()
    a = left / "same.txt"
    b = right / "same.txt"
    a.write_text("a", encoding="utf-8")
    b.write_text("b", encoding="utf-8")

    def measure(_directory: Path) -> float:
        return 1.0

    with pytest.raises(ValueError, match="duplicate file name"):
        filter_rounds([a, b], measure, rounds=1, split_by=10, stop_pct=None)


def test_filter_rounds_parameter_is_named_measure():
    params = inspect.signature(filter_rounds).parameters
    assert "measure" in params
    assert "metric" not in params
