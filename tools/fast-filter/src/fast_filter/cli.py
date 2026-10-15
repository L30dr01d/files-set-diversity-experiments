from __future__ import annotations

import argparse
import sys
from pathlib import Path

from fast_filter.reduce import ALGOS, reduce


def build_parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(
        prog="fast-filter",
        description="Reduce a directory of test files with FAST-R (inadequate / fixed budget).",
    )
    p.add_argument("files", type=Path, help="Directory of test files")
    p.add_argument(
        "--algo",
        required=True,
        help=f"FAST-R algorithm: {', '.join(sorted(ALGOS))}",
    )
    p.add_argument(
        "--percent",
        type=float,
        required=True,
        help="Target remaining size as a percent of the original suite",
    )
    return p


def main(argv: list[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    files_dir: Path = args.files
    algo: str = args.algo
    percent: float = args.percent

    if not files_dir.is_dir():
        print(f"error: not a directory: {files_dir}", file=sys.stderr)
        return 2
    if algo not in ALGOS:
        print(
            f"error: unknown algo {algo!r}. Allowed: {', '.join(sorted(ALGOS))}",
            file=sys.stderr,
        )
        return 2

    try:
        names = reduce(files_dir, algo, percent)
    except Exception as exc:  # noqa: BLE001
        print(f"error: {exc}", file=sys.stderr)
        return 1

    sys.stdout.write("".join(f"{name}\n" for name in names))
    return 0
