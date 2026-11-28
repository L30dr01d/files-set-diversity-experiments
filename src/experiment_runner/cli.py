from __future__ import annotations

import argparse
import json
import sys
from collections.abc import Sequence
from pathlib import Path
from tempfile import TemporaryDirectory

from experiment_runner.config import ConfigError, Experiment, execution_plan, load_config
from experiment_runner.plotly_figures import render
from experiment_runner.worker import run_worker


def matrix_payload(experiments: Sequence[Experiment]) -> dict:
    from spreadem import build_matrix

    rows = []
    for exp in experiments:
        if exp.disable_reason is not None:
            continue
        if not exp.clusters:
            rows.append({"id": exp.id, "type": exp.type})
        for index in range(len(exp.clusters)):
            rows.append({"id": f"{exp.id}--{index + 1}", "type": exp.type,
                         "experiment_id": exp.id, "cluster_index": index})
    return build_matrix(rows)


def _parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(prog="experiment_runner")
    sub = parser.add_subparsers(dest="command")
    sub.add_parser("matrix")
    run = sub.add_parser("run")
    run.add_argument("experiment_id")
    worker = sub.add_parser("worker")
    worker.add_argument("job_id")
    worker.add_argument("--results-dir", type=Path, required=True)
    aggregate = sub.add_parser("aggregate")
    aggregate.add_argument("--results-dir", type=Path, required=True)
    aggregate.add_argument("--output-dir", type=Path, required=True)
    sub.add_parser("editor")
    return parser


def main(argv: list[str] | None = None, *, root: Path | None = None) -> int:
    root = root or Path.cwd()
    args = _parser().parse_args(argv)
    try:
        if args.command == "editor":
            from .editor import serve
            serve(root)
            return 0
        experiments = load_config(root)
        if args.command == "worker":
            rows = matrix_payload(experiments)["include"]
            row = next((r for r in rows if r["id"] == args.job_id), None)
            if row is None:
                raise ConfigError(f"unknown cluster: {args.job_id}")
            exp = next(e for e in experiments if e.id == row.get("experiment_id", row["id"]))
            run_worker(execution_plan(exp), row.get("cluster_index", 0), root, args.results_dir)
            return 0
        if args.command == "aggregate":
            for exp in experiments:
                if exp.disable_reason is None:
                    render(execution_plan(exp), args.results_dir, args.output_dir)
            return 0
        if args.command == "matrix":
            print(json.dumps(matrix_payload(experiments), separators=(",", ":")))
            return 0
        match = next((exp for exp in experiments if exp.id == args.experiment_id), None)
        if match is None:
            raise ConfigError(f"unknown id: {args.experiment_id}")
        plan = execution_plan(match)
        with TemporaryDirectory() as tmp:
            for index in range(len(plan.clusters)):
                run_worker(plan, index, root, Path(tmp))
            render(plan, Path(tmp), root / "output")
        return 0
    except Exception as exc:  # noqa: BLE001
        print(f"error: {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
