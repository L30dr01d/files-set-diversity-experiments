from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TEXT = (ROOT / ".github" / "workflows" / "experiments.yml").read_text(encoding="utf-8")


def test_workflow_uses_matrix_output_and_uploads_both_plot_formats():
    assert "python -m experiment_runner matrix" in TEXT
    assert 'python -m experiment_runner run "$EXPERIMENT_ID"' in TEXT
    assert "EXPERIMENT_ID: ${{ matrix.id }}" in TEXT
    assert "fromJSON(needs.matrix.outputs.matrix)" in TEXT
    assert "if-no-files-found: error" in TEXT
    assert "output/${{ matrix.id }}.png" in TEXT
    assert "output/${{ matrix.id }}.svg" in TEXT
    assert "contents: read" in TEXT
    assert "fail-fast: false" in TEXT
    assert "workflow_dispatch" in TEXT


def test_workflow_uses_python_3_14_and_fastr_extra():
    assert 'python-version: "3.14"' in TEXT
    assert "python-version: \"3.13\"" not in TEXT
    assert "uv sync --extra fastr" in TEXT


def test_workflow_uses_verified_latest_stable_action_releases():
    releases = {
        "actions/checkout": "v7.0.1",
        "actions/setup-python": "v7.1.0",
        "astral-sh/setup-uv": "v10.3.2",
        "actions/upload-artifact": "v7.0.2",
        "actions/download-artifact": "v8.0.2",
        "actions/setup-node": "v7.1.0",
        "actions/configure-pages": "v6.0.0",
        "actions/upload-pages-artifact": "v5.0.0",
        "actions/deploy-pages": "v5.0.1",
    }
    for action, version in releases.items():
        assert f"uses: {action}@{version}\n" in TEXT


def test_workflow_builds_pages_from_complete_current_run_on_default_branch():
    site = TEXT.split("\n  site:\n")[1].split("\n  deploy:\n")[0]
    assert "needs: [matrix, experiment]" in site
    assert "github.ref == format('refs/heads/{0}', github.event.repository.default_branch)" in site
    assert "merge-multiple: true" in site
    assert "path: site/public/plots" in site
    assert "run-id:" not in site
    assert "github-token:" not in site
    assert 'node-version: "24"' in site
    assert "npm test" in site
    assert "npm run build" in site
    assert "SITE_URL: ${{ steps.pages.outputs.origin }}" in site
    assert "BASE_PATH: ${{ steps.pages.outputs.base_path }}" in site
    assert "path: site/dist" in site
    assert "pages: read" in site
    assert "pages: write" not in site
    assert "always()" in site
    assert "!cancelled()" in site


def test_workflow_serializes_deployment_without_freshness_check():
    deploy = TEXT.split("\n  deploy:\n")[1]
    assert "needs: site" in deploy
    assert "success()" in deploy
    assert "github.ref == format('refs/heads/{0}', github.event.repository.default_branch)" in deploy
    assert "pages: write" in deploy
    assert "id-token: write" in deploy
    assert "name: github-pages" in deploy
    assert "url: ${{ steps.deployment.outputs.page_url }}" in deploy
    assert "group: github-pages" in deploy
    assert "cancel-in-progress: false" in deploy
    assert "freshness" not in deploy
    assert "gh api" not in deploy
    assert "uses: actions/deploy-pages@v5.0.1\n        id: deployment" in deploy
    assert "always()" not in deploy


def test_empty_matrix_skips_experiments_but_allows_gallery():
    experiment = TEXT.split("\n  experiment:\n")[1].split("\n  site:\n")[0]
    site = TEXT.split("\n  site:\n")[1].split("\n  deploy:\n")[0]
    assert "if: needs.matrix.outputs.matrix != '{\"include\":[]}'" in experiment
    assert "always()" in site
    assert "!cancelled()" in site
    assert "needs.matrix.result == 'success'" in site
    assert "needs.experiment.result == 'success'" not in site
    assert "if: needs.experiment.result != 'skipped'" in site
    assert "continue-on-error: true" in site
