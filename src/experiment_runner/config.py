from __future__ import annotations

import json
from collections.abc import Sequence
from dataclasses import dataclass
from pathlib import Path

KNOWN_TYPES = frozenset({"score_per_measure"})


class ConfigError(ValueError):
    pass


@dataclass(frozen=True)
class Experiment:
    id: str
    type: str
    title: str
    datasets: tuple[str, ...]
    tools: tuple[str, ...]


def _require_nonempty_str(value: object, field: str) -> str:
    if not isinstance(value, str) or not value.strip():
        raise ConfigError(f"missing {field}")
    return value


def _require_name_tuple(value: object, field: str) -> tuple[str, ...]:
    if not isinstance(value, list) or not value:
        raise ConfigError(f"missing {field}")
    names: list[str] = []
    for item in value:
        if not isinstance(item, str) or not item.strip():
            raise ConfigError(f"missing {field}")
        names.append(item)
    return tuple(names)


def load_experiments(path: Path) -> list[Experiment]:
    if not path.is_file():
        raise ConfigError(f"missing experiments.json: {path}")
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except json.JSONDecodeError as exc:
        raise ConfigError(f"invalid experiments.json: {exc}") from exc
    if not isinstance(payload, dict) or not isinstance(payload.get("experiments"), list):
        raise ConfigError("missing experiments")
    experiments: list[Experiment] = []
    seen: set[str] = set()
    for raw in payload["experiments"]:
        if not isinstance(raw, dict):
            raise ConfigError("invalid experiment")
        exp_id = _require_nonempty_str(raw.get("id"), "id")
        if exp_id in seen:
            raise ConfigError(f"duplicate id: {exp_id}")
        seen.add(exp_id)
        exp_type = _require_nonempty_str(raw.get("type"), "type")
        if exp_type not in KNOWN_TYPES:
            raise ConfigError(f"unknown type: {exp_type}")
        experiments.append(
            Experiment(
                id=exp_id,
                type=exp_type,
                title=_require_nonempty_str(raw.get("title"), "title"),
                datasets=_require_name_tuple(raw.get("datasets"), "datasets"),
                tools=_require_name_tuple(raw.get("tools"), "tools"),
            )
        )
    return experiments


def validate_paths(root: Path, experiments: Sequence[Experiment]) -> None:
    for exp in experiments:
        for name in exp.datasets:
            path = root / "datasets" / name
            if not path.is_dir():
                raise ConfigError(f"dataset directory missing: {name}")
        for name in exp.tools:
            path = root / "tools" / name
            if not path.is_dir():
                raise ConfigError(f"tool directory missing: {name}")


def load_config(root: Path) -> list[Experiment]:
    experiments = load_experiments(root / "experiments.json")
    validate_paths(root, experiments)
    return experiments
