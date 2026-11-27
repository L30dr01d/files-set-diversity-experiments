from __future__ import annotations

from collections.abc import Mapping, Sequence
from pathlib import Path


def adequate_tick(kept: int, total: int) -> str:
    return f"adequate\n{kept} files, {round(100 * kept / total)}%"


def _sample_percent(kept: int, total: int) -> int:
    if total == 0:
        return 0
    return round(100 * kept / total)


def adequate_axis_label(samples: Sequence[Mapping]) -> str:
    kepts = [int(sample["kept"]) for sample in samples]
    percents = [
        _sample_percent(int(sample["kept"]), int(sample["total"])) for sample in samples
    ]
    low_kept, high_kept = min(kepts), max(kepts)
    low_percent, high_percent = min(percents), max(percents)
    file_part = (
        f"{low_kept} files" if low_kept == high_kept else f"{low_kept}-{high_kept} files"
    )
    percent_part = (
        f"{low_percent}%" if low_percent == high_percent else f"{low_percent}-{high_percent}%"
    )
    return f"adequate\n{file_part}, {percent_part}"


def iverilog_command(iverilog: Path, source: Path, out: Path) -> list[str]:
    return [str(iverilog), "-g2012", "-o", str(out), str(source)]


def verilator_command(verilator: Path, source: Path, mdir: Path) -> list[str]:
    return [
        str(verilator),
        "--cc",
        "--timing",
        "-Wno-fatal",
        "+1800-2023ext+sv",
        "--Mdir",
        str(mdir),
        str(source),
    ]


def profile_env(directory: Path) -> dict[str, str]:
    return {"LLVM_PROFILE_FILE": str(directory / "%m.profraw")}
