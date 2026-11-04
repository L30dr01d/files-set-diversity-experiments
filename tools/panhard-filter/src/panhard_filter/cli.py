from __future__ import annotations

import argparse
import sys
from pathlib import Path

from panhard_filter.filter import filter


def build_parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(
        prog="panhard-filter",
        description="Drop the least important file until panhard-xz would score the set lower.",
    )
    p.add_argument("files", type=Path, help="Directory of files to filter")
    return p


def main(argv: list[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    files_dir: Path = args.files
    if not files_dir.is_dir():
        print(f"error: not a directory: {files_dir}", file=sys.stderr)
        return 2
    try:
        names = filter(files_dir)
    except Exception as exc:  # noqa: BLE001
        print(f"error: {exc}", file=sys.stderr)
        return 1
    sys.stdout.write("".join(f"{name}\n" for name in names))
    return 0
