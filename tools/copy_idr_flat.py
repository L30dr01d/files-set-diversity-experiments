"""
Copy every .idr file from a project tree into a flat directory named {output}_{count}.

CLI usage:
    python copy_idr_flat.py --input ../deptycheck --output datasets/031_deptycheck_original
"""

import argparse
import shutil
from pathlib import Path


def _is_under_git(path: Path, root: Path) -> bool:
    return ".git" in path.relative_to(root).parts


def _flat_name(path: Path, root: Path) -> str:
    return "__".join(path.relative_to(root).parts)


def copy_idr_flat(src: Path, output_prefix: Path) -> Path:
    files = sorted(
        path
        for path in src.rglob("*.idr")
        if path.is_file() and not _is_under_git(path, src)
    )
    dest = output_prefix.with_name(f"{output_prefix.name}_{len(files)}")
    if dest.exists():
        raise FileExistsError(dest)
    dest.mkdir(parents=True)
    for path in files:
        shutil.copy2(path, dest / _flat_name(path, src))
    return dest


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Copy all .idr files from a project into a flat {output}_{count} directory."
    )
    parser.add_argument("--input", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()

    dest = copy_idr_flat(args.input, args.output)
    print(f"Copied {dest.name.rsplit('_', 1)[-1]} .idr files -> {dest}")


if __name__ == "__main__":
    main()
