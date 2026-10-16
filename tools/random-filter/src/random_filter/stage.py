from __future__ import annotations

from collections.abc import Callable, Sequence
from pathlib import Path
from tempfile import TemporaryDirectory


def score_paths(files: Sequence[Path], measure: Callable[[Path], float]) -> float:
    names = [path.name for path in files]
    if len(names) != len(set(names)):
        duplicate = next(name for name in names if names.count(name) > 1)
        raise ValueError(f"duplicate file name: {duplicate}")
    for path in files:
        if not path.is_file():
            raise ValueError(f"not a file: {path}")
    with TemporaryDirectory(prefix="random-filter-") as tmp:
        dest = Path(tmp)
        for path in files:
            (dest / path.name).symlink_to(path.resolve())
        return measure(dest)
