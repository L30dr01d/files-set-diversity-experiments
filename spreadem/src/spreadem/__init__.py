"""Build a GitHub Actions matrix from ordered job specifications."""

import json
from collections.abc import Sequence


def build_matrix(rows: Sequence[dict]) -> dict:
    if len(rows) > 256:
        raise ValueError(f"matrix has {len(rows)} jobs; GitHub allows 256")
    seen = set()
    for row in rows:
        job = row.get("id") if isinstance(row, dict) else None
        if not isinstance(job, str) or not job.strip() or job in seen:
            raise ValueError(f"invalid or duplicate job id: {job!r}")
        seen.add(job)
    matrix = {"include": list(rows)}
    try:
        json.dumps(matrix, allow_nan=False)
    except (TypeError, ValueError) as exc:
        raise ValueError("matrix metadata must be JSON compatible") from exc
    return matrix
