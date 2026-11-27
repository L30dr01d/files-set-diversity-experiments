import json
import os
import shutil
import subprocess
import sys

import pytest

from experiment_runner import instrumented_analyzers as runner


def test_summary_matches_multiobject_llvm_and_merges_mcdc_pairs(tmp_path):
    for tool in ("clang", "llvm-profdata", "llvm-cov", "jq"):
        if not shutil.which(tool):
            pytest.skip(f"{tool} unavailable")
    flags = ["-fprofile-instr-generate", "-fcoverage-mapping", "-fcoverage-mcdc"]
    generated = tmp_path / "obj_dir" / "generated.h"
    generated.parent.mkdir()
    generated.write_text("int generated(int a, int b) { return a && b; }\n")
    images = []
    for name, source in {
        "decision": "int main(int n,char **v) {\n return n > 1 && n < 3;\n}\n",
        "extra": (
            "int main(int n,char **v) {\n if (n == 1)\n  return 0;\n return 1;\n}\n"
            '#include "obj_dir/generated.h"\n'
        ),
    }.items():
        c_file = tmp_path / f"{name}.c"
        c_file.write_text(source)
        image = tmp_path / name
        build = subprocess.run(["clang", *flags, c_file, "-o", image], capture_output=True)
        if build.returncode and b"unknown argument" in build.stderr and b"fcoverage-mcdc" in build.stderr:
            pytest.skip("clang lacks MC/DC instrumentation")
        build.check_returncode()
        images.append(image)

    raw_dir = tmp_path / "files, with commas"
    raw_dir.mkdir()
    profiles = []
    for index, (image, arguments) in enumerate([(images[0], []), (images[0], ["x"]), (images[1], [])]):
        raw = raw_dir / f"{index}.profraw"
        subprocess.run([image, *arguments], env={**os.environ, "LLVM_PROFILE_FILE": str(raw)},
                       check=False)
        profiles.append(raw)

    for raw in profiles[:2]:
        assert runner._summary(images, [raw], tmp_path)["mcdc"] == 0

    merged = tmp_path / "expected.profdata"
    subprocess.run(["llvm-profdata", "merge", "-sparse", *profiles, "-o", merged], check=True)
    report = subprocess.check_output(["llvm-cov", "export", "-summary-only", images[0],
                                      "-object", images[1], "-instr-profile", merged,
                                      "-ignore-filename-regex=^/usr/|obj_dir"])
    totals = json.loads(report)["data"][0]["totals"]
    assert 0 < totals["lines"]["percent"] < 100
    assert totals["mcdc"]["percent"] == 50
    assert runner._summary(images, profiles, tmp_path) == {
        "line": totals["lines"]["percent"], "mcdc": totals["mcdc"]["percent"]
    }
    assert runner._summary(images, [], tmp_path) == {"line": 0, "mcdc": 0}


@pytest.mark.parametrize("output,status", [
    ({"lines": {"percent": 100}}, 0),
    ({"lines": {"percent": 100}, "mcdc": {"percent": 20}}, 1),
])
def test_summary_rejects_missing_fields_and_failed_export(tmp_path, monkeypatch, output, status):
    if not shutil.which("jq"):
        pytest.skip("jq unavailable")
    payload = json.dumps({"data": [{"totals": output}]})
    command = [sys.executable, "-c", f"print({payload!r}); raise SystemExit({status})"]
    monkeypatch.setattr(runner, "_export_command", lambda *_: command)
    with pytest.raises(subprocess.CalledProcessError):
        runner._summary([], [], tmp_path)
