# ci-experiments

Config-driven diversity experiments. Edit `experiments.json`, push, and browse the interactive plots on GitHub Pages. Use the PNG and SVG buttons there to export the current figure.

```bash
uv sync --python 3.14 --extra fastr
uv run pytest
uv run python -m experiment_runner matrix
uv run python -m experiment_runner run 19_150_sv_panhard_filter_rni
```

Also install dependencies for Panhard:
  - `brew install xz bc` on macOS
  - `sudo apt-get install xz-utils bc` on Debian/Ubuntu


Experiment types:

- `score_per_measure` — scatter per measure.
- `measure_per_set` — bar chart per dataset.
- `score_for_fastr` — FAST++ / FAST-CS budget lines.
- `score_for_random_filter` — leftover-% boxes; `tools[0]` filters, every tool is plotted.
- `score_for_panhard_dpi` and `score_for_panhard_rni` — file-count plots using the selected ranking. A shaded band extends one residual on either side of the Panhard measure, and a dashed line marks where filtering would normally stop.
- `coverage_with_filter` — one dataset with ten fresh line and MC/DC measurements per budget (100%, 75%, 50%, 25%). The figure shows coverage by budget and files kept for line, MC/DC, and joint adequacy. Verilator and Icarus each have a row, followed by a row of adequacy results for a shared suite that preserves coverage in both tools.
- `coverage_with_filter_panhard_dpi` and `coverage_with_filter_panhard_rni` — one column per dataset with diversity and its residual band, line coverage, and MC/DC coverage. Instrumented Icarus and Verilator run on every subset in the full trace, including steps past the marked Panhard stop. Set `"tools": []` for coverage experiments to use the built-in tools.

Coverage experiments require matching MC/DC-capable Clang and LLVM tools plus `jq`. Each draw runs independently. The runner merges its raw profiles with `llvm-profdata merge` and reads the line and MC/DC percentages from one `llvm-cov export -summary-only` report per analyzer.

The measure plots use consistent colors for Panhard (blue), Levassor (orange), Poisson (green), and NCD1 (red). Coverage plots use Icarus `C0` and Verilator `C1`. The shared-suite row in `coverage_with_filter` uses `C2`.
Spawned workers are capped at 4 GiB so a runaway score cannot take down the GitHub runner.

Every experiment produces an interactive Plotly figure. **Fit to data** adjusts each Y-axis to its observations. **Full range** shows 0–100% on coverage and files-kept panels and 0–1 on normalized score panels. Each job artifact includes a self-contained HTML preview of its assigned measurements. Open `<job-id>.html` offline to inspect the job, including any gaps for failed measurements. The accompanying JSON records use the same record fields: `experiment`, `cluster`, `dataset`, `column`, and `payload`. The payload holds the measurements specific to that experiment type. The gallery aggregates only the JSON records to build the full experiment figure.

## Clustered experiments

Run `uv run python -m experiment_runner editor` from the repository root. Select an experiment, choose a job, check datasets and tools, then **Apply assignment**. Download the validated JSON and replace `experiments.json` when ready. Each rectangle creates one Actions job. Unassigned combinations are omitted. The editor counts all enabled jobs, including legacy entries, against the 256-job matrix limit.

The first clustered figure, `16_deptycheck`, plots 60 measurements together across its configured jobs. CI uploads completed cells before aggregation. A missing worker artifact leaves its planned cells empty. Each figure has its own **Fit to data** and **Full range** controls. Keep the generated HTML and its sibling `plotly.min.js` together.

```bash
uv run python -m experiment_runner run 16_deptycheck
# Or exercise a single cluster and inspect the partial figure:
uv run python -m experiment_runner worker 16_deptycheck--1 --results-dir results
uv run python -m experiment_runner aggregate --results-dir results --output-dir output
```

Use a fresh results directory for each plan/run. For clustered FASTR experiments, columns select algorithms and the experiment-level scorers apply to every budget. Coverage uses a single column. Random-filter configurations can set `filter_tool` to keep the same selection rule across clusters.

## Experiment gallery

The static site in `site/` uses Astro and locally bundled Blades CSS.

```bash
mkdir -p site/public/plots
cp output/*.{html,js} site/public/plots/
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
