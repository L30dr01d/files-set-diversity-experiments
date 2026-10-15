import hashlib

from levassor_metric.shingles import WINDOW, file_shingles, hash_window, iter_windows


def test_window_length_is_16() -> None:
    assert WINDOW == 16


def test_hash_window_is_blake2b_uint64() -> None:
    window = b"0123456789abcdef"
    expected = int.from_bytes(
        hashlib.blake2b(window, digest_size=8).digest(),
        "big",
    )
    assert hash_window(window) == expected


def test_empty_bytes_have_no_windows() -> None:
    assert iter_windows(b"") == []
    assert file_shingles(b"") == set()


def test_short_file_is_one_whole_window() -> None:
    data = b"hello"
    assert iter_windows(data) == [data]
    assert file_shingles(data) == {hash_window(data)}


def test_long_file_has_len_minus_15_overlapping_windows() -> None:
    data = bytes(range(32))
    windows = iter_windows(data)
    assert len(windows) == 32 - 15
    assert windows[0] == data[0:16]
    assert windows[-1] == data[16:32]
    assert file_shingles(data) == {hash_window(window) for window in windows}
