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
`measure_per_set`, `score_for_fastr`, and `score_for_random_filter` use the same color for each measure: `panhard-v3-measure` blue, `levassor-measure` orange, `poisson-measure` green, `ncd1-measure` red.
Each measure `score`, each FAST-R `reduce`, and each random-filter `filter_subset` call is killed after 1 hour and recorded as `null`.
A raising measure, reduce, or filter is the same: stderr warning, `null`, continue.
A worker that dies (including memory exhaustion) is also `null`; the rest of that experiment still runs.
Spawned workers are capped at 4 GiB so a runaway score cannot take down the GitHub runner.

Each run writes `output/<id>.png`.

Dataset helper scripts:

```bash
python tools/copy_file.py --input /path/to/file --output-dir datasets/027_one_sv_file_25 --count 25
python tools/copy_idr_flat.py --input ../deptycheck --output datasets/031_deptycheck_original
python tools/rename_lowercase_idents.py --input-dir datasets/031_deptycheck_original_768 --output-dir datasets/032_deptycheck_renamed_768 --mode same-length
python tools/rename_lowercase_idents.py --input-dir datasets/031_deptycheck_original_768 --output-dir datasets/033_deptycheck_renamed128_768 --mode 128
python tools/combine_datasets.py \
  datasets/031_deptycheck_original_768 \
  datasets/032_deptycheck_renamed_same_length_768 \
  datasets/033_deptycheck_renamed128_768 \
  datasets/034_deptycheck_renamed128_2_768
```

`copy_idr_flat` writes to `{output}_{count}` (file count appended). `rename_lowercase_idents` keeps keywords and Capitalized words, renames lowercase-starting tokens; `--mode same-length` or `128`; optional `--seed` (default 0). `combine_datasets` writes every pair, then every triple, then all four; copied files are prefixed with the source id.
