# ci-experiments

Config-driven diversity experiments. Edit `experiments.json`, push, download PNG artifacts from the Actions run.

```bash
uv sync
uv run pytest
uv run python -m experiment_runner matrix
uv run python -m experiment_runner run algo_similar_vs_diverse
```

CI runs Python 3.14. `score_for_fastr` needs FAST-R (`uv sync --extra fastr` on 3.14). Panhard needs `xz` and `bc` on PATH.

Experiment types: `score_per_measure` (scatter per metric), `measure_per_set` (bar chart per dataset), `score_for_fastr` (FAST++ / FAST-CS budget lines).
Each metric `score` and each FAST-R `reduce` is killed after 20 minutes and recorded as `null`.
A raising metric or reduce is the same: stderr warning, `null`, continue.
The rest of that experiment still runs.

Each run writes `output/<id>.png`.
