from pathlib import Path

from random_filter.knee import knee_cutoff


def test_knee_keeps_files_after_the_curve_break():
    paths = [Path(name) for name in ("a", "b", "c", "d", "e")]
    counts = {paths[0]: 10, paths[1]: 9, paths[2]: 2, paths[3]: 1, paths[4]: 0}
    index, kept = knee_cutoff(counts)
    assert index == 2
    assert kept == [paths[2], paths[3], paths[4]]


def test_flat_counts_keep_every_file_in_input_order():
    paths = [Path(name) for name in ("a", "b", "c", "d")]
    counts = {path: 5 for path in paths}
    index, kept = knee_cutoff(counts)
    assert index == 0
    assert kept == paths


def test_fewer_than_three_files_keeps_input_order():
    paths = [Path("a"), Path("b")]
    index, kept = knee_cutoff({paths[0]: 3, paths[1]: 1})
    assert index == 0
    assert kept == paths
