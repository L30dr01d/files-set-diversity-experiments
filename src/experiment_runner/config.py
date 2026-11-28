from __future__ import annotations

import json
import re
from itertools import product
from collections.abc import Sequence
from dataclasses import dataclass, replace
from pathlib import Path

KNOWN_TYPES = frozenset(
    {
        "score_per_measure",
        "measure_per_set",
        "score_for_fastr",
        "score_for_random_filter",
        "score_for_panhard_dpi",
        "score_for_panhard_rni",
        "coverage_with_filter",
        "coverage_with_filter_panhard_dpi",
        "coverage_with_filter_panhard_rni",
    }
)


class ConfigError(ValueError):
    pass


FASTR_ALGORITHMS = ("FAST++", "FAST-CS")


@dataclass(frozen=True)
class Cluster:
    datasets: tuple[str, ...]
    tools: tuple[str, ...]

    def cells(self):
        return product(self.datasets, self.tools or ("coverage",))


@dataclass(frozen=True)
class Experiment:
    id: str
    type: str
    title: str
    datasets: tuple[str, ...]
    tools: tuple[str, ...]
    disable_reason: str | None = None
    clusters: tuple[Cluster, ...] = ()
    scorers: tuple[str, ...] = ()
    filter_tool: str | None = None


def execution_plan(exp: Experiment) -> Experiment:
    """A whole-experiment job is one implicit rectangle."""
    if exp.clusters:
        return exp
    tools = exp.tools
    scorers = ()
    if exp.type == "score_for_fastr":
        scorers, tools = tools, FASTR_ALGORITHMS
    elif exp.type.startswith("coverage_"):
        tools = ()
    elif exp.type.startswith("score_for_panhard") and not tools:
        tools = ("panhard-measure",)
    return replace(exp, tools=tools, scorers=scorers, clusters=(Cluster(exp.datasets, tools),))


def _require_nonempty_str(value: object, field: str) -> str:
    if not isinstance(value, str) or not value.strip():
        raise ConfigError(f"missing {field}")
    return value


def _require_name_tuple(
    value: object, field: str, *, allow_empty: bool = False
) -> tuple[str, ...]:
    if not isinstance(value, list) or (not value and not allow_empty):
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
    return parse_config(payload)


def parse_config(payload: dict) -> list[Experiment]:
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
        if not re.fullmatch(r"[A-Za-z0-9_-]+", exp_id):
            raise ConfigError(f"invalid experiment id: {exp_id}")
        filter_tool = None
        clusters = []
        scorers = ()
        if "runtime_clusters" in raw:
            if "datasets" in raw or "tools" in raw:
                raise ConfigError("choose either runtime_clusters or legacy datasets/tools")
            definitions = raw["runtime_clusters"]
            if not isinstance(definitions, list) or not definitions:
                raise ConfigError("missing runtime_clusters")
            cells = set()
            for definition in definitions:
                if not isinstance(definition, dict):
                    raise ConfigError("invalid cluster")
                datasets = _require_name_tuple(definition.get("datasets"), "datasets")
                coverage = exp_type.startswith("coverage_")
                tools = _require_name_tuple(definition.get("tools", []), "tools", allow_empty=coverage)
                if coverage and tools:
                    raise ConfigError("coverage clusters take only datasets")
                cluster = Cluster(datasets, tools)
                for cell in cluster.cells():
                    if cell in cells:
                        raise ConfigError(f"{exp_id}: overlapping assignment {cell}")
                    cells.add(cell)
                clusters.append(cluster)
            datasets = tuple(dict.fromkeys(d for c in clusters for d in c.datasets))
            tools = tuple(dict.fromkeys(t for c in clusters for t in c.tools))
            if exp_type == "score_for_random_filter":
                filter_tool = _require_nonempty_str(raw.get("filter_tool", tools[0]), "filter_tool")
            if exp_type == "score_for_fastr":
                scorers = _require_name_tuple(raw.get("scorers"), "scorers")
                if set(tools).difference(FASTR_ALGORITHMS):
                    raise ConfigError("unknown FASTR algorithm")
        else:
            datasets = _require_name_tuple(raw.get("datasets"), "datasets")
            tools = _require_name_tuple(raw.get("tools"), "tools", allow_empty=True)
        experiments.append(
            Experiment(
                id=exp_id,
                type=exp_type,
                title=_require_nonempty_str(raw.get("title"), "title"),
                datasets=datasets,
                tools=tools,
                clusters=tuple(clusters),
                scorers=scorers,
                filter_tool=filter_tool,
                disable_reason=(
                    _require_nonempty_str(raw["disable_reason"], "disable_reason")
                    if "disable_reason" in raw else None
                ),
            )
        )
    return experiments


def validate_paths(root: Path, experiments: Sequence[Experiment]) -> None:
    for exp in experiments:
        for name in exp.datasets:
            if Path(name).name != name or name in (".", ".."):
                raise ConfigError(f"invalid dataset: {name}")
            path = root / "datasets" / name
            if not path.is_dir():
                raise ConfigError(f"dataset directory missing: {name}")
        names = exp.scorers or exp.tools
        if exp.filter_tool:
            names = (*names, exp.filter_tool)
        for name in names:
            if exp.clusters and not name.endswith("-measure"):
                raise ConfigError(f"unknown scoring tool: {name}")
            if Path(name).name != name or name in (".", ".."):
                raise ConfigError(f"invalid tool: {name}")
            path = root / "tools" / name
            if not path.is_dir():
                raise ConfigError(f"tool directory missing: {name}")


def load_config(root: Path) -> list[Experiment]:
    experiments = load_experiments(root / "experiments.json")
    validate_paths(root, experiments)
    return experiments
