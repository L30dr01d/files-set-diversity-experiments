"""
Rename lowercase-starting identifiers in files, leaving keywords and Capitalized words.

Two modes:
    same-length  — replacement has the same length as the original
    128          — replacement is 128 letters

CLI usage:
    python rename_lowercase_idents.py --input-dir DIR --output-dir DIR --mode same-length
    python rename_lowercase_idents.py --input-dir DIR --output-dir DIR --mode 128
"""

from __future__ import annotations

import argparse
import re
import string
from pathlib import Path
from random import Random

IDENT = re.compile(r"[A-Za-z][A-Za-z0-9_']*")

KEYWORDS = frozenset(
    {
        "as",
        "auto",
        "case",
        "constructor",
        "covering",
        "data",
        "default",
        "do",
        "else",
        "export",
        "failing",
        "forall",
        "if",
        "implementation",
        "implicit",
        "impossible",
        "import",
        "in",
        "infix",
        "infixl",
        "infixr",
        "interface",
        "let",
        "module",
        "mutual",
        "namespace",
        "of",
        "open",
        "parameters",
        "partial",
        "prefix",
        "private",
        "public",
        "record",
        "rewrite",
        "then",
        "total",
        "using",
        "where",
        "with",
    }
)

MODES = ("same-length", "128")


def _should_rename(token: str) -> bool:
    return token[0].islower() and token not in KEYWORDS


def _random_name(rng: Random, length: int, forbidden: set[str]) -> str:
    while True:
        chars = [rng.choice(string.ascii_lowercase)]
        chars.extend(rng.choice(string.ascii_letters) for _ in range(length - 1))
        name = "".join(chars)
        if name not in forbidden and name not in KEYWORDS:
            return name


def _length_for(token: str, mode: str) -> int:
    if mode == "same-length":
        return len(token)
    if mode == "128":
        return 128
    raise ValueError(f"unknown mode {mode!r}")


def rename_idents(text: str, rng: Random, mode: str) -> str:
    mapping: dict[str, str] = {}
    forbidden: set[str] = set()

    def repl(match: re.Match[str]) -> str:
        token = match.group(0)
        if not _should_rename(token):
            return token
        if token not in mapping:
            mapping[token] = _random_name(rng, _length_for(token, mode), forbidden)
            forbidden.add(mapping[token])
        return mapping[token]

    return IDENT.sub(repl, text)


def rename_dir(input_dir: Path, output_dir: Path, mode: str, seed: int = 0) -> None:
    output_dir.mkdir(parents=True, exist_ok=True)
    rng = Random(seed)
    names = sorted(path.name for path in input_dir.iterdir() if path.is_file())
    for name in names:
        text = (input_dir / name).read_text(encoding="utf-8")
        (output_dir / name).write_text(
            rename_idents(text, rng, mode), encoding="utf-8"
        )


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Rename lowercase identifiers; keep keywords and Capitalized words."
    )
    parser.add_argument("--input-dir", type=Path, required=True)
    parser.add_argument("--output-dir", type=Path, required=True)
    parser.add_argument("--mode", choices=MODES, required=True)
    parser.add_argument("--seed", type=int, default=0)
    args = parser.parse_args()
    rename_dir(args.input_dir, args.output_dir, mode=args.mode, seed=args.seed)
    print(f"Renamed ({args.mode}, seed={args.seed}): {args.input_dir} -> {args.output_dir}")


if __name__ == "__main__":
    main()
