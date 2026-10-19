"""
Combine dataset directories into every pair, then every triple, …, then all N.

CLI usage:
    python tools/combine_datasets.py \\
      datasets/031_deptycheck_original_768 \\
      datasets/032_deptycheck_renamed_same_length_768 \\
      datasets/033_deptycheck_renamed128_768 \\
      datasets/034_deptycheck_renamed128_2_768
"""

from __future__ import annotations

import argparse
import itertools
import re
import shutil
from collections.abc import Sequence
from pathlib import Path

SOURCE_ID = re.compile(r"^(?P<id>\d+)_.+")


def source_id(path: Path) -> str:
    match = SOURCE_ID.fullmatch(path.name)
    if match is None:
        raise ValueError(f"directory name has no leading digits_ id: {path.name}")
    return match.group("id")


def combinations_in_order(paths: Sequence[Path]) -> list[tuple[Path, ...]]:
    result: list[tuple[Path, ...]] = []
    for k in range(2, len(paths) + 1):
        result.extend(itertools.combinations(paths, k))
    return result


def _regular_files(src: Path) -> list[Path]:
    files = [
        path
        for path in src.iterdir()
        if path.is_file() and not path.is_symlink() and not path.name.startswith(".")
    ]
    return sorted(files, key=lambda path: path.name)


def combine(
    paths: Sequence[Path],
    output_parent: Path,
    start: int = 35,
) -> list[Path]:
    if len(paths) < 2:
        raise ValueError("need at least two dataset directories")
    for path in paths:
        if not path.is_dir():
            raise NotADirectoryError(path)
    ids = [source_id(path) for path in paths]
    if len(set(ids)) != len(ids):
        raise ValueError(f"duplicate source ids: {ids}")
    files_by_src = {path: _regular_files(path) for path in paths}
    for path, files in files_by_src.items():
        if not files:
            raise ValueError(f"no files to copy in {path}")

    dests: list[Path] = []
    number = start
    for combo in combinations_in_order(paths):
        combo_ids = [source_id(path) for path in combo]
        count = sum(len(files_by_src[path]) for path in combo)
        dest = output_parent / f"{number:03d}_{'+'.join(combo_ids)}_{count}"
        if dest.exists():
            if dest.is_file() or dest.is_symlink():
                raise FileExistsError(dest)
            shutil.rmtree(dest)
        dest.mkdir(parents=True)
        for path in combo:
            sid = source_id(path)
            for src_file in files_by_src[path]:
                shutil.copy2(src_file, dest / f"{sid}__{src_file.name}")
        dests.append(dest)
        number += 1
    return dests


def main() -> None:
    parser = argparse.ArgumentParser(
        description=(
            "Combine dataset directories into every pair, then every triple, "
            "then the full set. Copied files are prefixed with the source id."
        )
    )
    parser.add_argument(
        "inputs",
        nargs="+",
        type=Path,
        help="Dataset directories, in the order their ids should appear.",
    )
    parser.add_argument(
        "--output-parent",
        type=Path,
        default=None,
        help="Directory that receives new datasets (default: parent of the first input).",
    )
    parser.add_argument(
        "--start",
        type=int,
        default=35,
        help="First output number (default: 35).",
    )
    args = parser.parse_args()
    if len(args.inputs) < 2:
        parser.error("need at least two dataset directories")
    output_parent = (
        args.output_parent if args.output_parent is not None else args.inputs[0].parent
    )
    dests = combine(args.inputs, output_parent, start=args.start)
    print(f"Wrote {len(dests)} datasets -> {output_parent}")


if __name__ == "__main__":
    main()
