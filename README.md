# ci-experiments

Config-driven diversity experiments. Edit `experiments.json`, push, download PNG artifacts from the Actions run.

```bash
uv sync
uv run pytest
uv run python -m experiment_runner matrix
uv run python -m experiment_runner run algo_similar_vs_diverse
```

Panhard needs `xz` and `bc` on PATH.

Each metric call is killed after 20 minutes and recorded as `null`. Other datasets and metrics still run.
