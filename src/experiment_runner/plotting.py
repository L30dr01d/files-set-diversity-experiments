from __future__ import annotations

MEASURE_COLORS = {
    "panhard-measure": "C0",
    "levassor-measure": "C1",
    "poisson-measure": "C2",
    "ncd1-measure": "C3",
}


def tool_color(name: str, index: int) -> str:
    return MEASURE_COLORS.get(name, f"C{index}")
