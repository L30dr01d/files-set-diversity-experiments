import json
from pathlib import Path

import pytest

from experiment_runner.config import (
    KNOWN_TYPES,
    ConfigError,
    Experiment,
    load_config,
    load_experiments,
    validate_paths,
)


def _write(path: Path, payload: object) -> Path:
    path.write_text(json.dumps(payload), encoding="utf-8")
    return path


def test_known_types_include_four_experiment_types():
    assert KNOWN_TYPES == frozenset(
        {
            "score_per_measure",
            "measure_per_set",
            "score_for_fastr",
            "score_for_random_filter",
        }
    )


def test_load_experiments_reads_fields(tmp_path: Path):
    _write(
        tmp_path / "experiments.json",
        {
            "experiments": [
                {
                    "id": "ex1",
                    "type": "score_per_measure",
                    "title": "Hello viewers",
                    "datasets": ["016_algos_java_1_task_10_variants_10"],
                    "tools": ["levassor-metric"],
                }
            ]
        },
    )
    loaded = load_experiments(tmp_path / "experiments.json")
    assert loaded == [
        Experiment(
            id="ex1",
            type="score_per_measure",
            title="Hello viewers",
            datasets=("016_algos_java_1_task_10_variants_10",),
            tools=("levassor-metric",),
        )
    ]


def test_duplicate_id_raises(tmp_path: Path):
    entry = {
        "id": "ex1",
        "type": "score_per_measure",
        "title": "t",
        "datasets": ["a"],
        "tools": ["b"],
    }
    _write(tmp_path / "experiments.json", {"experiments": [entry, dict(entry)]})
    with pytest.raises(ConfigError, match="duplicate"):
        load_experiments(tmp_path / "experiments.json")


def test_missing_title_raises(tmp_path: Path):
    _write(
        tmp_path / "experiments.json",
        {
            "experiments": [
                {
                    "id": "ex1",
                    "type": "score_per_measure",
                    "datasets": ["a"],
                    "tools": ["b"],
                }
            ]
        },
    )
    with pytest.raises(ConfigError, match="title"):
        load_experiments(tmp_path / "experiments.json")


def test_empty_datasets_raises(tmp_path: Path):
    _write(
        tmp_path / "experiments.json",
        {
            "experiments": [
                {
                    "id": "ex1",
                    "type": "score_per_measure",
                    "title": "t",
                    "datasets": [],
                    "tools": ["b"],
                }
            ]
        },
    )
    with pytest.raises(ConfigError, match="datasets"):
        load_experiments(tmp_path / "experiments.json")


def test_load_experiments_accepts_new_types(tmp_path: Path):
    _write(
        tmp_path / "experiments.json",
        {
            "experiments": [
                {
                    "id": "bars",
                    "type": "measure_per_set",
                    "title": "Bars",
                    "datasets": ["ds-a"],
                    "tools": ["levassor-metric"],
                },
                {
                    "id": "fastr",
                    "type": "score_for_fastr",
                    "title": "Fastr",
                    "datasets": ["ds-a"],
                    "tools": ["levassor-metric"],
                },
                {
                    "id": "rand",
                    "type": "score_for_random_filter",
                    "title": "Random filter",
                    "datasets": ["ds-a"],
                    "tools": ["levassor-metric"],
                },
            ]
        },
    )
    loaded = load_experiments(tmp_path / "experiments.json")
    assert [exp.type for exp in loaded] == [
        "measure_per_set",
        "score_for_fastr",
        "score_for_random_filter",
    ]


def test_unknown_type_raises(tmp_path: Path):
    _write(
        tmp_path / "experiments.json",
        {
            "experiments": [
                {
                    "id": "ex1",
                    "type": "budget_curve",
                    "title": "t",
                    "datasets": ["a"],
                    "tools": ["b"],
                }
            ]
        },
    )
    with pytest.raises(ConfigError, match="budget_curve"):
        load_experiments(tmp_path / "experiments.json")


def test_invalid_json_raises(tmp_path: Path):
    (tmp_path / "experiments.json").write_text("{", encoding="utf-8")
    with pytest.raises(ConfigError, match="invalid"):
        load_experiments(tmp_path / "experiments.json")


def test_missing_file_raises(tmp_path: Path):
    with pytest.raises(ConfigError, match="experiments.json"):
        load_experiments(tmp_path / "experiments.json")


def test_validate_paths_requires_directories(tmp_path: Path):
    exp = Experiment(
        id="ex1",
        type="score_per_measure",
        title="t",
        datasets=("missing-ds",),
        tools=("missing-tool",),
    )
    with pytest.raises(ConfigError, match="missing-ds"):
        validate_paths(tmp_path, [exp])


def test_load_config_accepts_existing_dirs(tmp_path: Path):
    (tmp_path / "datasets" / "ds-a").mkdir(parents=True)
    (tmp_path / "tools" / "tool-a").mkdir(parents=True)
    _write(
        tmp_path / "experiments.json",
        {
            "experiments": [
                {
                    "id": "ex1",
                    "type": "score_per_measure",
                    "title": "t",
                    "datasets": ["ds-a"],
                    "tools": ["tool-a"],
                }
            ]
        },
    )
    loaded = load_config(tmp_path)
    assert loaded[0].id == "ex1"
