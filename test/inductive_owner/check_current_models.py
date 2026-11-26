import json
import subprocess
import sys
import tempfile
from pathlib import Path

here = Path(__file__).resolve().parent
root = here.parent.parent
compiler = sys.argv[1]
origins = {
    entry["construct"]: entry["source"]
    for entry in json.loads((here / "out/source_range_info.json").read_text())
}
for suffix in ("__abs_rep_current", "__abs_model_current", "__abs_rep_current_model",
               "__abs_model_current_now", "__abs_model_current_snapshot"):
    assert origins["class_CurrentModelOwner" + suffix] == origins["class_CurrentModelOwner__inv"]
    assert "class_OwnedCell" + suffix not in origins
    assert "class_OwnedCallHolder" + suffix not in origins
assert origins["class_OwnedCallHolder__inv_restore"] == origins["class_OwnedCallHolder__inv"]
assert "class_CurrentModelOwner__inv_restore" not in origins
positive = (here / "out/Func_CurrentModelOwner_Drain.fst").read_text()
assert "__abs_rep_current_model" in positive
assert "__abs_model_current_now var_this 1.0R" in positive
assert "__abs_model_current vrep_" in positive
assert "spec_CurrentModelOwner_Value (reveal pre_this)" in positive
assert "spec_CurrentModelOwner_Value var_this" not in positive
fixed = (here / "out/Func_CurrentModelOwner_StepThenCount.fst").read_text()
assert "__abs_model_current_snapshot var_this 1.0R" in fixed
assert "spec_CurrentModelOwner_Value (reveal vCurrentModelOwner_" in fixed

source = (here / "CurrentModels.cs").read_text()
good = "Pal.Assert(this.Value == Pal.Old(this.Value) - completed);"
assert source.count(good) == 1
source = source.replace("CurrentModelOwner", "NegativeCurrentModelOwner").replace(
    good, "Pal.Assert(this.Value == Pal.Old(this.Value));"
)
with tempfile.TemporaryDirectory(prefix="pal-current-model-") as temporary:
    directory = Path(temporary)
    fixture = directory / "NegativeCurrentModels.cs"
    fixture.write_text(source)
    translated = subprocess.run(
        [compiler, "--reference", str(here / "out"), "-o", temporary, str(fixture)],
        text=True, capture_output=True,
    )
    assert translated.returncode == 0, translated.stdout + translated.stderr
    command = [
        str(root / "tools/run-fstar.sh"), "--include", temporary,
        "--include", str(here / "out"), "--include", str(here / "_cache"),
        "--include", str(root / "pulse/_cache"), "--cache_checked_modules",
        "--cache_dir", temporary, "--already_cached", "*",
    ]
    for module in ("Class_NegativeCurrentModelOwner", "Func_NegativeCurrentModelOwner_Step"):
        checked = subprocess.run(command + [str(directory / (module + ".fst"))], text=True, capture_output=True)
        assert checked.returncode == 0, checked.stdout + checked.stderr
    target = directory / "Func_NegativeCurrentModelOwner_Drain.fst"
    checked = subprocess.run(command + [str(target)], text=True, capture_output=True)
    failure = checked.stdout + checked.stderr
    assert checked.returncode != 0, "A stale entry-state assertion was accepted after mutation"
    assert "Assertion failed" in failure, failure
    assertion = next(line for line in target.read_text().splitlines() if "assert (pure" in line)
    assert "__abs_model_current" in assertion and "pre_this" in assertion, assertion

with tempfile.TemporaryDirectory(prefix="pal-unsupported-current-model-") as temporary:
    translated = subprocess.run(
        [compiler, "-o", temporary, str(here / "UnsupportedCurrentModel.cs.in")],
        text=True, capture_output=True,
    )
    diagnostics = translated.stdout + translated.stderr
    assert translated.returncode != 0, "Unsupported current array-model binding was accepted"
    assert "Current model observations of this open mutable representation" in diagnostics, diagnostics
    unsupported_origins = json.loads((Path(temporary) / "source_range_info.json").read_text())
    assert not any("__abs_model_current" in entry["construct"] for entry in unsupported_origins)

array_source = (here / "UnsupportedCurrentModel.cs.in").read_text()
array_source = array_source.replace("private int[] items;", "private int[] items; private int marker;").replace(
    "items = new int[1];", "items = new int[1]; marker = 0;"
)
loop_start = array_source.index("        int i = 0;")
array_source = array_source[:loop_start] + "{body}\n    }\n}\n"
array_source += """
public static class ArrayObservers
{
    [Spec] public static int Read(int n) => n;
    [Lemma, Ensures("n == n"), System.Diagnostics.Conditional("PAL")]
    public static void Remember(int n) { }
}
"""
for name, body, accepted in (
    ("pristine", "Pal.Assert(this.Length == 1); items[0] = 42;", True),
    ("pure-observers", "ArrayObservers.Remember(marker); Pal.Assert(ArrayObservers.Read(marker) == marker); "
     "Pal.Assert(this.Length == 1); items[0] = 42;", True),
    ("mutated", "items[0] = 42; Pal.Assert(this.Length == 1);", False),
    ("alias", "var alias = items; alias[0] = 42; Pal.Assert(this.Length == 1);", False),
):
    with tempfile.TemporaryDirectory(prefix="pal-current-array-" + name) as temporary:
        directory = Path(temporary)
        fixture = directory / "CurrentArray.cs"
        fixture.write_text(array_source.replace("{body}", body))
        translated = subprocess.run(
            [compiler, "-o", temporary, str(fixture)], text=True, capture_output=True,
        )
        diagnostics = translated.stdout + translated.stderr
        assert (translated.returncode == 0) == accepted, diagnostics
        if not accepted:
            assert "Current model observations of this open mutable representation" in diagnostics, diagnostics
            continue
        command = [
            str(root / "tools/run-fstar.sh"), "--include", temporary,
            "--include", str(root / "pulse/_cache"), "--cache_checked_modules",
            "--cache_dir", temporary, "--already_cached", "*",
        ]
        for module in ("Class_UnsupportedCurrentModel", "Let_ArrayObservers_Read",
                       "Let_ArrayObservers_Remember", "Func_UnsupportedCurrentModel_Mutate"):
            checked = subprocess.run(
                command + [str(directory / (module + ".fst"))], text=True, capture_output=True,
            )
            assert checked.returncode == 0, checked.stdout + checked.stderr

print("Current models: projections/decreases and Old checked; stale assertion and unsupported shape rejected")
