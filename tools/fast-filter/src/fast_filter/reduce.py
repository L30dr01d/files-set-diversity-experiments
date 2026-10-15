from __future__ import annotations

import tempfile
from pathlib import Path

from fast_filter.budget import budget_from_percent
from fast_filter.suite import list_test_files, write_suite_file

ALGOS: frozenset[str] = frozenset({"FAST++", "FAST-CS", "FAST-pw"})


def _run_inadequate(algo: str, suite: str, budget: int) -> list[int]:
    import fastr

    if algo == "FAST++":
        _p, _r, sel = fastr.fastPlusPlus(suite, dim=10, B=budget)
    elif algo == "FAST-CS":
        _p, _r, sel = fastr.fastCS(suite, dim=10, B=budget)
    elif algo == "FAST-pw":
        _p, _r, sel = fastr.fast_pw(
            suite, r=1, b=10, bbox=True, k=5, memory=True, B=budget
        )
    else:
        raise ValueError(f"Unknown algo {algo!r}")
    return [int(i) for i in sel]


def _selection_to_basenames(selection: list[int], basenames: list[str]) -> list[str]:
    result: list[str] = []
    for tc_id in selection:
        idx = tc_id - 1
        if idx < 0 or idx >= len(basenames):
            raise ValueError(f"selection id {tc_id} out of range")
        result.append(basenames[idx])
    return result


def reduce(files_dir: Path, algo: str, target_percent: float) -> list[str]:
    if algo not in ALGOS:
        allowed = ", ".join(sorted(ALGOS))
        raise ValueError(f"Unknown algo {algo!r}. Allowed: {allowed}")
    paths = list_test_files(files_dir)
    basenames = [p.name for p in paths]
    budget = budget_from_percent(len(basenames), target_percent)
    with tempfile.TemporaryDirectory(prefix="fast-filter-") as tmp:
        suite_path = Path(tmp) / "suite.txt"
        write_suite_file(paths, suite_path)
        sel = _run_inadequate(algo, str(suite_path), budget)
    names = _selection_to_basenames(sel, basenames)
    unknown = [n for n in names if n not in set(basenames)]
    if unknown:
        raise ValueError(f"FAST-R kept unknown basenames: {unknown[:5]}")
    if len(names) != budget:
        raise ValueError(
            f"FAST-R kept {len(names)} files, expected budget {budget}"
        )
    return names
