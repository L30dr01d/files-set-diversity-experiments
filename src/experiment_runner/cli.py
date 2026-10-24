from __future__ import annotations

import argparse
import json
import sys
from collections.abc import Sequence
from pathlib import Path

from experiment_runner.config import ConfigError, Experiment, load_config
from experiment_runner.measure_per_set import run_measure_per_set
from experiment_runner.score_for_fastr import run_score_for_fastr
from experiment_runner.score_for_random_filter import run_score_for_random_filter
from experiment_runner.score_per_measure import run_score_per_measure


def matrix_payload(experiments: Sequence[Experiment]) -> dict:
    return {"include": [{"id": exp.id} for exp in experiments if exp.disable_reason is None]}


def _parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(prog="experiment_runner")
    sub = parser.add_subparsers(dest="command")
    sub.add_parser("matrix")
    run = sub.add_parser("run")
    run.add_argument("experiment_id")
    return parser


def main(argv: list[str] | None = None, *, root: Path | None = None) -> int:
    root = root or Path.cwd()
    args = _parser().parse_args(argv)
    if args.command not in {"matrix", "run"}:
        print("error: command must be matrix or run", file=sys.stderr)
        return 1
    try:
        experiments = load_config(root)
        if args.command == "matrix":
            print(json.dumps(matrix_payload(experiments), separators=(",", ":")))
            return 0
        match = next((exp for exp in experiments if exp.id == args.experiment_id), None)
        if match is None:
            raise ConfigError(f"unknown id: {args.experiment_id}")
        if match.type == "score_per_measure":
            run_score_per_measure(match, root, output_dir=root / "output")
            return 0
        if match.type == "measure_per_set":
            run_measure_per_set(match, root, output_dir=root / "output")
            return 0
        if match.type == "score_for_fastr":
            run_score_for_fastr(match, root, output_dir=root / "output")
            return 0
        if match.type == "score_for_random_filter":
            run_score_for_random_filter(match, root, output_dir=root / "output")
            return 0
        raise ConfigError(f"unknown type: {match.type}")
    except Exception as exc:  # noqa: BLE001
        print(f"error: {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
