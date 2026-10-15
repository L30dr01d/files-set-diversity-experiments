from __future__ import annotations

import importlib
from collections.abc import Callable
from pathlib import Path

from experiment_runner.config import ConfigError


def dataset_dir(root: Path, name: str) -> Path:
    return root / "datasets" / name


def tool_dir(root: Path, name: str) -> Path:
    return root / "tools" / name


def tool_module_name(name: str) -> str:
    return name.replace("-", "_")


def load_score(name: str) -> Callable[[Path], float]:
    module_name = tool_module_name(name)
    try:
        module = importlib.import_module(module_name)
    except ImportError as exc:
        raise ConfigError(f"cannot import tool {name!r}: {exc}") from exc
    fn = getattr(module, "score", None)
    if not callable(fn):
        raise ConfigError(f"tool {name!r} has no score()")
    return fn
