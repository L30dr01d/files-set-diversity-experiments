from __future__ import annotations

import argparse
import sys
from pathlib import Path

from panhard_filter.filter import filter_dir


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(prog="panhard-filter")
    parser.add_argument("--dont-stop", action="store_true")
    parser.add_argument("folder", type=Path)
    args = parser.parse_args(argv)
    try:
        result = filter_dir(args.folder, dont_stop=args.dont_stop)
    except (ValueError, RuntimeError, OSError) as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 1
    for path in result.kept:
        print(path)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
