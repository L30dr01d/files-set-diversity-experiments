"""
Simplest possible Caesar cipher applied to files.

Rotates letters (a-z, A-Z) by `shift`, preserving case. All non-letter
characters (digits, punctuation, whitespace) are passed through unchanged,
so the output is always valid UTF-8.

CLI usage:
    python caesar_cipher.py --input-dir /path/to/src --output-dir /path/to/dst [--shift 3]
"""

import argparse
import os
from pathlib import Path


def apply_caesar(data: bytes, shift: int) -> bytes:
    result = bytearray(len(data))
    for i, b in enumerate(data):
        if ord("a") <= b <= ord("z"):
            result[i] = ord("a") + (b - ord("a") + shift) % 26
        elif ord("A") <= b <= ord("Z"):
            result[i] = ord("A") + (b - ord("A") + shift) % 26
        else:
            result[i] = b
    return bytes(result)


def apply_caesar_to_dir(input_dir: Path, output_dir: Path, shift: int = 3) -> None:
    for name in os.listdir(input_dir):
        src = input_dir / name
        if not src.is_file():
            continue
        data = src.read_bytes()
        (output_dir / name).write_bytes(apply_caesar(data, shift))


def main() -> None:
    parser = argparse.ArgumentParser(description="Apply Caesar cipher to all files in a directory.")
    parser.add_argument("--input-dir", type=Path, required=True)
    parser.add_argument("--output-dir", type=Path, required=True)
    parser.add_argument("--shift", type=int, default=3)
    args = parser.parse_args()

    args.output_dir.mkdir(parents=True, exist_ok=True)
    apply_caesar_to_dir(args.input_dir, args.output_dir, args.shift)
    print(f"Caesar cipher (shift={args.shift}) applied: {args.input_dir} -> {args.output_dir}")


if __name__ == "__main__":
    main()
