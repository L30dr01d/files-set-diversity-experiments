import importlib.util
import re
from pathlib import Path
from random import Random

SCRIPT = Path(__file__).resolve().parents[1] / "tools" / "rename_lowercase_idents.py"

IDENT = re.compile(r"[A-Za-z][A-Za-z0-9_']*")


def _load():
    spec = importlib.util.spec_from_file_location("rename_lowercase_idents", SCRIPT)
    assert spec is not None and spec.loader is not None
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def _idents(text: str) -> list[str]:
    return IDENT.findall(text)


def test_preserves_keywords_and_capitalized_renames_lowercase():
    mod = _load()
    src = (
        "module UseGen\n"
        "public export\n"
        "data Foo : Type where\n"
        "  MkFoo : allQImpl -> Foo\n"
        "fin_uni_gen : Nat\n"
    )
    out = mod.rename_idents(src, Random(0), "same-length")
    assert "module" in out
    assert "public" in out
    assert "export" in out
    assert "data" in out
    assert "where" in out
    assert "UseGen" in out
    assert "Foo" in out
    assert "MkFoo" in out
    assert "Type" in out
    assert "Nat" in out
    assert "allQImpl" not in out
    assert "fin_uni_gen" not in out
    assert "allQImpl" in _idents(src)
    lowered = [t for t in _idents(out) if t[0].islower() and t not in mod.KEYWORDS]
    assert all(t != "allQImpl" and t != "fin_uni_gen" for t in lowered)


def test_same_length_replacements_are_letters_starting_lowercase():
    mod = _load()
    src = "allQImpl : foo -> allQImpl\n"
    out = mod.rename_idents(src, Random(1), "same-length")
    mapping = {
        orig: repl
        for orig, repl in zip(_idents(src), _idents(out))
        if orig[0].islower() and orig not in mod.KEYWORDS
    }
    assert mapping["allQImpl"]
    assert mapping["foo"]
    assert mapping["allQImpl"] != mapping["foo"]
    assert _idents(src).count("allQImpl") == 2
    assert _idents(out).count(mapping["allQImpl"]) == 2
    for orig, repl in mapping.items():
        assert len(repl) == len(orig)
        assert repl[0].islower()
        assert repl.isalpha()


def test_fixed_128_replacements():
    mod = _load()
    src = "allQImpl : foo\n"
    out = mod.rename_idents(src, Random(2), "128")
    repls = [
        t
        for t, orig in zip(_idents(out), _idents(src))
        if orig[0].islower() and orig not in mod.KEYWORDS
    ]
    assert len(repls) == 2
    for repl in repls:
        assert len(repl) == 128
        assert repl[0].islower()
        assert repl.isalpha()


def test_fresh_mapping_per_file(tmp_path: Path):
    mod = _load()
    src_dir = tmp_path / "in"
    dest_dir = tmp_path / "out"
    src_dir.mkdir()
    (src_dir / "a.idr").write_text("foo : Nat\n", encoding="utf-8")
    (src_dir / "b.idr").write_text("foo : Nat\n", encoding="utf-8")
    mod.rename_dir(src_dir, dest_dir, mode="same-length", seed=0)
    a = (dest_dir / "a.idr").read_text(encoding="utf-8")
    b = (dest_dir / "b.idr").read_text(encoding="utf-8")
    a_foo = next(t for t in _idents(a) if t != "Nat")
    b_foo = next(t for t in _idents(b) if t != "Nat")
    assert a_foo != "foo"
    assert b_foo != "foo"
    assert a_foo != b_foo


def test_renames_words_inside_comments():
    mod = _load()
    src = "-- foo bar\n"
    out = mod.rename_idents(src, Random(3), "same-length")
    assert "foo" not in out
    assert "bar" not in out
