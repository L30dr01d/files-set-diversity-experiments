"""
Copy one file N times into a directory with numbered names.

CLI usage:
    python copy_file.py --input /path/to/file --output-dir /path/to/dst --count 25
"""

import argparse
import shutil
from pathlib import Path


def copy_n_times(src: Path, output_dir: Path, count: int) -> None:
    output_dir.mkdir(parents=True, exist_ok=True)
    for i in range(1, count + 1):
        dest = output_dir / f"{src.stem}_{i:03d}{src.suffix}"
        shutil.copy2(src, dest)


def main() -> None:
    parser = argparse.ArgumentParser(description="Copy one file N times into a directory.")
    parser.add_argument("--input", type=Path, required=True)
    parser.add_argument("--output-dir", type=Path, required=True)
    parser.add_argument("--count", type=int, required=True)
    args = parser.parse_args()

    copy_n_times(args.input, args.output_dir, args.count)
    print(f"Copied {args.input} x {args.count} -> {args.output_dir}")


if __name__ == "__main__":
    main()
