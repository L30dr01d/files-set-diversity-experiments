# ci-experiments

Config-driven diversity experiments. Edit `experiments.json`, push, download PNG artifacts from the Actions run.

```bash
uv sync
uv run pytest
uv run python -m experiment_runner matrix
uv run python -m experiment_runner run algo_similar_vs_diverse
```

CI runs Python 3.14. `score_for_fastr` needs FAST-R (`uv sync --extra fastr` on 3.14). Panhard needs `xz` and `bc` on PATH.

Experiment types: `score_per_measure` (scatter per measure), `measure_per_set` (bar chart per dataset), `score_for_fastr` (FAST++ / FAST-CS budget lines), `score_for_random_filter` (random-filter steps; `tools[0]` filters, every tool is plotted).
Each measure `score`, each FAST-R `reduce`, and each random-filter `filter_subset` call is killed after 20 minutes and recorded as `null`.
A raising measure, reduce, or filter is the same: stderr warning, `null`, continue.
A worker that dies (including memory exhaustion) is also `null`; the rest of that experiment still runs.
Spawned workers are capped at 4 GiB so a runaway score cannot take down the GitHub runner.

Each run writes `output/<id>.png`.
