from pathlib import Path


def list_test_files(files_dir: Path) -> list[Path]:
    if not files_dir.is_dir():
        raise ValueError(f"not a directory: {files_dir}")
    paths = sorted(
        (p for p in files_dir.iterdir() if p.is_file()),
        key=lambda p: p.name,
    )
    if not paths:
        raise ValueError(f"no tests found in {files_dir}")
    return paths


def _flatten_text(path: Path) -> str:
    text = path.read_text(encoding="utf-8", errors="replace")
    return " ".join(text.splitlines())


def write_suite_file(paths: list[Path], dest: Path) -> None:
    with dest.open("w", encoding="utf-8") as out:
        for path in paths:
            out.write(_flatten_text(path))
            out.write("\n")
