import importlib.util
import sys
from pathlib import Path

import pytest

SCRIPT = Path(__file__).resolve().parents[1] / "tools" / "combine_datasets.py"


def _load():
    spec = importlib.util.spec_from_file_location("combine_datasets", SCRIPT)
    assert spec is not None and spec.loader is not None
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def test_source_id_reads_leading_digits():
    mod = _load()
    assert mod.source_id(Path("datasets/031_deptycheck_original_768")) == "031"
    assert mod.source_id(Path("035_031+032_1536")) == "035"


def test_source_id_rejects_name_without_digits_underscore_rest():
    mod = _load()
    with pytest.raises(ValueError, match="no leading digits_ id"):
        mod.source_id(Path("deptycheck_original"))
    with pytest.raises(ValueError, match="no leading digits_ id"):
        mod.source_id(Path("031"))
    with pytest.raises(ValueError, match="no leading digits_ id"):
        mod.source_id(Path("031_"))


def test_combinations_in_order_pairs_then_triples_then_all():
    mod = _load()
    paths = [
        Path("031_a"),
        Path("032_b"),
        Path("033_c"),
        Path("034_d"),
    ]
    combos = mod.combinations_in_order(paths)
    ids = [tuple(mod.source_id(p) for p in combo) for combo in combos]
    assert ids == [
        ("031", "032"),
        ("031", "033"),
        ("031", "034"),
        ("032", "033"),
        ("032", "034"),
        ("033", "034"),
        ("031", "032", "033"),
        ("031", "032", "034"),
        ("031", "033", "034"),
        ("032", "033", "034"),
        ("031", "032", "033", "034"),
    ]


def _write_dataset(parent: Path, name: str, files: dict[str, bytes]) -> Path:
    dest = parent / name
    dest.mkdir()
    for filename, content in files.items():
        (dest / filename).write_bytes(content)
    return dest


def test_combine_three_datasets_writes_pairs_then_triple(tmp_path: Path):
    payload = {
        "a.idr": b"one",
        "b.idr": b"two",
        ".DS_Store": b"mac",
    }
    a = _write_dataset(tmp_path, "031_orig", {**payload, **{"a.idr": b"A1", "b.idr": b"A2"}})
    b = _write_dataset(tmp_path, "032_renamed", {**payload, **{"a.idr": b"B1", "b.idr": b"B2"}})
    c = _write_dataset(tmp_path, "033_renamed128", {**payload, **{"a.idr": b"C1", "b.idr": b"C2"}})
    (a / "nested").mkdir()
    (a / "nested" / "skip.idr").write_bytes(b"nope")

    dests = _load().combine([a, b, c], tmp_path, start=35)

    assert [p.name for p in dests] == [
        "035_031+032_4",
        "036_031+033_4",
        "037_032+033_4",
        "038_031+032+033_6",
    ]
    first = dests[0]
    names = sorted(p.name for p in first.iterdir())
    assert names == ["031__a.idr", "031__b.idr", "032__a.idr", "032__b.idr"]
    assert (first / "031__a.idr").read_bytes() == b"A1"
    assert (first / "032__b.idr").read_bytes() == b"B2"
    assert not (first / ".DS_Store").exists()
    assert not any(p.name.endswith("skip.idr") for p in first.iterdir())
    triple = dests[-1]
    assert sorted(p.name for p in triple.iterdir()) == [
        "031__a.idr",
        "031__b.idr",
        "032__a.idr",
        "032__b.idr",
        "033__a.idr",
        "033__b.idr",
    ]


def test_combine_two_inputs_writes_one_pair_and_no_triple(tmp_path: Path):
    a = _write_dataset(tmp_path, "031_orig", {"a.idr": b"A", "b.idr": b"B"})
    b = _write_dataset(tmp_path, "032_renamed", {"a.idr": b"C", "b.idr": b"D"})

    dests = _load().combine([a, b], tmp_path, start=35)

    assert [p.name for p in dests] == ["035_031+032_4"]
    assert not (tmp_path / "036_031+032_4").exists()


def test_combine_replaces_existing_destination_directory(tmp_path: Path):
    a = _write_dataset(tmp_path, "031_orig", {"a.idr": b"A", "b.idr": b"B"})
    b = _write_dataset(tmp_path, "032_renamed", {"a.idr": b"C", "b.idr": b"D"})
    leftover = tmp_path / "035_031+032_4"
    leftover.mkdir()
    (leftover / "old copy.idr").write_bytes(b"stale")

    dests = _load().combine([a, b], tmp_path, start=35)

    assert dests == [leftover]
    names = sorted(p.name for p in leftover.iterdir())
    assert names == ["031__a.idr", "031__b.idr", "032__a.idr", "032__b.idr"]
    assert not (leftover / "old copy.idr").exists()


def test_combine_rejects_duplicate_ids(tmp_path: Path):
    a = _write_dataset(tmp_path, "031_orig", {"a.idr": b"A"})
    b = _write_dataset(tmp_path, "031_other", {"a.idr": b"B"})
    with pytest.raises(ValueError, match="duplicate source ids"):
        _load().combine([a, b], tmp_path, start=35)


def test_combine_rejects_fewer_than_two_inputs(tmp_path: Path):
    a = _write_dataset(tmp_path, "031_orig", {"a.idr": b"A"})
    with pytest.raises(ValueError, match="need at least two dataset directories"):
        _load().combine([a], tmp_path, start=35)


def test_combine_rejects_input_that_is_not_a_directory(tmp_path: Path):
    a = _write_dataset(tmp_path, "031_orig", {"a.idr": b"A"})
    lone = tmp_path / "032_file"
    lone.write_bytes(b"nope")
    with pytest.raises(NotADirectoryError):
        _load().combine([a, lone], tmp_path, start=35)


def test_combine_rejects_directory_without_source_id(tmp_path: Path):
    a = _write_dataset(tmp_path, "031_orig", {"a.idr": b"A"})
    b = _write_dataset(tmp_path, "nope", {"a.idr": b"B"})
    with pytest.raises(ValueError, match="no leading digits_ id"):
        _load().combine([a, b], tmp_path, start=35)


def test_combine_rejects_source_with_only_hidden_files(tmp_path: Path):
    a = _write_dataset(tmp_path, "031_orig", {"a.idr": b"A"})
    b = _write_dataset(tmp_path, "032_empty", {".DS_Store": b"mac"})
    with pytest.raises(ValueError, match="no files to copy"):
        _load().combine([a, b], tmp_path, start=35)


def test_combine_fails_if_destination_exists_as_file(tmp_path: Path):
    a = _write_dataset(tmp_path, "031_orig", {"a.idr": b"A", "b.idr": b"B"})
    b = _write_dataset(tmp_path, "032_renamed", {"a.idr": b"C", "b.idr": b"D"})
    blocker = tmp_path / "035_031+032_4"
    blocker.write_bytes(b"keep")
    with pytest.raises(FileExistsError):
        _load().combine([a, b], tmp_path, start=35)
    assert blocker.read_bytes() == b"keep"


def test_main_defaults_output_parent_to_first_input_parent(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
):
    a = _write_dataset(tmp_path, "031_orig", {"a.idr": b"A", "b.idr": b"B"})
    b = _write_dataset(tmp_path, "032_renamed", {"a.idr": b"C", "b.idr": b"D"})
    monkeypatch.setattr(
        sys,
        "argv",
        ["combine_datasets.py", str(a), str(b)],
    )
    _load().main()
    dest = tmp_path / "035_031+032_4"
    assert dest.is_dir()
    assert sorted(p.name for p in dest.iterdir()) == [
        "031__a.idr",
        "031__b.idr",
        "032__a.idr",
        "032__b.idr",
    ]


def test_main_honors_output_parent_and_start(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
):
    a = _write_dataset(tmp_path, "031_orig", {"a.idr": b"A", "b.idr": b"B"})
    b = _write_dataset(tmp_path, "032_renamed", {"a.idr": b"C", "b.idr": b"D"})
    out = tmp_path / "merged"
    monkeypatch.setattr(
        sys,
        "argv",
        [
            "combine_datasets.py",
            str(a),
            str(b),
            "--output-parent",
            str(out),
            "--start",
            "40",
        ],
    )
    _load().main()
    dest = out / "040_031+032_4"
    assert dest.is_dir()


def test_main_errors_on_one_input(tmp_path: Path, monkeypatch: pytest.MonkeyPatch):
    a = _write_dataset(tmp_path, "031_orig", {"a.idr": b"A"})
    monkeypatch.setattr(sys, "argv", ["combine_datasets.py", str(a)])
    with pytest.raises(SystemExit):
        _load().main()
