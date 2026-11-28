from __future__ import annotations

import argparse
import json
import sys
from collections.abc import Sequence
from pathlib import Path

from experiment_runner.config import ConfigError, Experiment, load_config
from experiment_runner.coverage_with_filter import run_coverage_with_filter
from experiment_runner.coverage_with_filter_panhard import run_coverage_with_filter_panhard
from experiment_runner.measure_per_set import run_measure_per_set
from experiment_runner.score_for_fastr import run_score_for_fastr
from experiment_runner.score_for_panhard import run_score_for_panhard
from experiment_runner.score_for_random_filter import run_score_for_random_filter
from experiment_runner.score_per_measure import run_score_per_measure


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
            from .worker import run_worker
            rows = matrix_payload(experiments)["include"]
            row = next((r for r in rows if r["id"] == args.job_id and "cluster_index" in r), None)
            if row is None:
                raise ConfigError(f"unknown cluster: {args.job_id}")
            exp = next(e for e in experiments if e.id == row["experiment_id"])
            run_worker(exp, row["cluster_index"], root, args.results_dir)
            return 0
        if args.command == "aggregate":
            from .plotly_figures import render
            for exp in experiments:
                if exp.clusters and exp.disable_reason is None:
                    render(exp, args.results_dir, args.output_dir)
            return 0
        if args.command == "matrix":
            print(json.dumps(matrix_payload(experiments), separators=(",", ":")))
            return 0
        match = next((exp for exp in experiments if exp.id == args.experiment_id), None)
        if match is None:
            raise ConfigError(f"unknown id: {args.experiment_id}")
        if match.clusters:
            from tempfile import TemporaryDirectory
            from .worker import run_worker
            from .plotly_figures import render
            with TemporaryDirectory() as tmp:
                for index in range(len(match.clusters)):
                    run_worker(match, index, root, Path(tmp))
                render(match, Path(tmp), root / "output")
            return 0
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
        if match.type in ("score_for_panhard_dpi", "score_for_panhard_rni"):
            run_score_for_panhard(
                match, root, ranking=match.type.rsplit("_", 1)[1], output_dir=root / "output"
            )
            return 0
        if match.type == "coverage_with_filter":
            run_coverage_with_filter(match, root, output_dir=root / "output")
            return 0
        if match.type in ("coverage_with_filter_panhard_dpi", "coverage_with_filter_panhard_rni"):
            run_coverage_with_filter_panhard(
                match, root, ranking=match.type.rsplit("_", 1)[1], output_dir=root / "output"
            )
            return 0
        raise ConfigError(f"unknown type: {match.type}")
    except Exception as exc:  # noqa: BLE001
        print(f"error: {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
