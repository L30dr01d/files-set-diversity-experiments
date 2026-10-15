import importlib.util
from pathlib import Path

SCRIPT = Path(__file__).resolve().parents[1] / "tools" / "copy_file.py"


def _load():
    spec = importlib.util.spec_from_file_location("copy_file", SCRIPT)
    assert spec is not None and spec.loader is not None
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def test_copy_n_times_writes_numbered_identical_copies(tmp_path: Path):
    src = tmp_path / "seed.sv"
    src.write_text("module seed;\nendmodule\n", encoding="utf-8")
    dest = tmp_path / "out"

    _load().copy_n_times(src, dest, 3)

    names = sorted(p.name for p in dest.iterdir())
    assert names == ["seed_001.sv", "seed_002.sv", "seed_003.sv"]
    for name in names:
        assert (dest / name).read_bytes() == src.read_bytes()
