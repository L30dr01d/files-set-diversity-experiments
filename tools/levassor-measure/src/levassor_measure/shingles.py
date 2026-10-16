from __future__ import annotations

import hashlib

WINDOW = 16


def hash_window(window: bytes) -> int:
    return int.from_bytes(hashlib.blake2b(window, digest_size=8).digest(), "big")


def iter_windows(data: bytes, w: int = WINDOW) -> list[bytes]:
    if not data:
        return []
    if len(data) < w:
        return [data]
    return [data[i : i + w] for i in range(len(data) - w + 1)]


def file_shingles(data: bytes, w: int = WINDOW) -> set[int]:
    return {hash_window(window) for window in iter_windows(data, w)}
