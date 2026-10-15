from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TEXT = (ROOT / ".github" / "workflows" / "experiments.yml").read_text(encoding="utf-8")


def test_workflow_uses_matrix_output_and_uploads_png():
    assert "python -m experiment_runner matrix" in TEXT
    assert "python -m experiment_runner run ${{ matrix.id }}" in TEXT
    assert "fromJSON(needs.matrix.outputs.matrix)" in TEXT
    assert "if-no-files-found: error" in TEXT
    assert "output/${{ matrix.id }}.png" in TEXT
    assert "contents: read" in TEXT
    assert "fail-fast: false" in TEXT
    assert "workflow_dispatch" in TEXT


def test_workflow_uses_python_3_14_and_fastr_extra():
    assert 'python-version: "3.14"' in TEXT
    assert "python-version: \"3.13\"" not in TEXT
    assert "uv sync --extra fastr" in TEXT
