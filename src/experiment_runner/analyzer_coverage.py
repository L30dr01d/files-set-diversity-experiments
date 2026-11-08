from __future__ import annotations

from collections.abc import Sequence
from dataclasses import dataclass
from pathlib import Path


@dataclass(frozen=True)
class ImageCoverage:
    line_hits: frozenset[str]
    line_universe: frozenset[str]
    mcdc_hits: frozenset[str]
    mcdc_universe: frozenset[str]


def _union(*groups: frozenset[str]) -> frozenset[str]:
    return frozenset().union(*groups)


def combine_images(parts: Sequence[ImageCoverage]) -> ImageCoverage:
    return ImageCoverage(
        line_hits=_union(*(part.line_hits for part in parts)),
        line_universe=_union(*(part.line_universe for part in parts)),
        mcdc_hits=_union(*(part.mcdc_hits for part in parts)),
        mcdc_universe=_union(*(part.mcdc_universe for part in parts)),
    )


def _percent(numerator: int, denominator: int) -> float:
    if denominator == 0:
        return 0.0
    return 100 * numerator / denominator


def subset_percents(
    files: Sequence[ImageCoverage], universe: ImageCoverage
) -> tuple[float, float]:
    line_hits = _union(*(part.line_hits for part in files))
    mcdc_hits = _union(*(part.mcdc_hits for part in files))
    return (
        _percent(len(line_hits), len(universe.line_universe)),
        _percent(len(mcdc_hits), len(universe.mcdc_universe)),
    )


def adequate_tick(kept: int, total: int) -> str:
    return f"adequate\n{kept} files, {round(100 * kept / total)}%"


def whitebox_line(coverage: ImageCoverage) -> str:
    line_tokens = [f"L{hit_id}" for hit_id in sorted(coverage.line_hits)]
    mcdc_tokens = [f"M{hit_id}" for hit_id in sorted(coverage.mcdc_hits)]
    return " ".join(line_tokens + mcdc_tokens)


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


def _condition_flags(record: list) -> list[bool]:
    for item in record:
        if isinstance(item, list) and all(isinstance(flag, bool) for flag in item):
            return item
    return []


def hits_from_llvm_export(payload: dict) -> ImageCoverage:
    line_hits: set[str] = set()
    line_universe: set[str] = set()
    mcdc_hits: set[str] = set()
    mcdc_universe: set[str] = set()
    for source_file in payload["data"][0]["files"]:
        filename = source_file["filename"]
        if "obj_dir" in filename:
            continue
        name = Path(filename).name
        for segment in source_file["segments"]:
            # [line, col, count, hasCount, isRegionEntry, isGapRegion]
            if not segment[3] or segment[5]:
                continue
            line_id = f"{name}:{segment[0]}"
            line_universe.add(line_id)
            if segment[2] > 0:
                line_hits.add(line_id)
        for record in source_file["mcdc_records"]:
            line, column = record[0], record[1]
            for index, flag in enumerate(_condition_flags(record)):
                condition_id = f"{name}:{line}:{column}:{index}"
                mcdc_universe.add(condition_id)
                if flag:
                    mcdc_hits.add(condition_id)
    return ImageCoverage(
        line_hits=frozenset(line_hits),
        line_universe=frozenset(line_universe),
        mcdc_hits=frozenset(mcdc_hits),
        mcdc_universe=frozenset(mcdc_universe),
    )
