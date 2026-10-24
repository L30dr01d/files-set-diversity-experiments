# ci-experiments

Config-driven diversity experiments. Edit `experiments.json`, push, and browse the latest plots on GitHub Pages or download PNG/SVG artifacts from the Actions run.

```bash
uv sync --python 3.14 --extra fastr
uv run pytest
uv run python -m experiment_runner matrix
uv run python -m experiment_runner run 05_super_random_3
```

Run these commands from the repository root. Python 3.14 and the `fastr` extra
install all experiment dependencies, including FAST-R. Plain `uv sync` installs
the base dependencies only. CI also uses Python 3.14. Panhard needs `xz` and `bc`
on PATH (`brew install xz bc` on macOS or `sudo apt-get install xz-utils bc` on
Debian/Ubuntu).

Experiment types: `score_per_measure` (scatter per measure), `measure_per_set` (bar chart per dataset), `score_for_fastr` (FAST++ / FAST-CS budget lines), `score_for_random_filter` (leftover-% boxes; `tools[0]` filters, every tool is plotted).
`measure_per_set`, `score_for_fastr`, and `score_for_random_filter` use the same color for each measure: `panhard-measure` blue, `levassor-measure` orange, `poisson-measure` green, `ncd1-measure` red.
Each measure `score`, each FAST-R `reduce`, and each random-filter `filter_subset` call is killed after 6 hours (21600 seconds) and recorded as `null`.
A raising measure, reduce, or filter is the same: stderr warning, `null`, continue.
A worker that dies (including memory exhaustion) is also `null`; the rest of that experiment still runs.
Spawned workers are capped at 4 GiB so a runaway score cannot take down the GitHub runner.

Each run writes `output/<id>.png` and `output/<id>.svg` from the same plot.

## Experiment gallery

The static site in `site/` uses Astro and locally bundled Blades CSS.

```bash
mkdir -p site/public/plots
cp output/*.{png,svg} site/public/plots/
npm --prefix site install
npm --prefix site test
npm --prefix site run dev
```

`npm --prefix site run build` writes `site/dist/`; `npm --prefix site run preview`
serves that production build. To test a repository subpath:

```bash
SITE_URL=https://example.github.io BASE_PATH=/ci-experiments/ npm --prefix site run build
```

## Dataset helper scripts

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

Set an experiment's optional `disable_reason` to a nonempty string to exclude it from CI and display the reason in the gallery. Manual runs remain available.

