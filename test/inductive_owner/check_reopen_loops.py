import subprocess
import sys
import tempfile
from pathlib import Path

here = Path(__file__).resolve().parent
root = here.parent.parent
compiler = sys.argv[1]
for method in ("Loop", "ReadOnlyLoop"):
    text = (here / f"out/Func_ReopenOwner_{method}.fst").read_text()
    invariant = text.split("invariant exists*", 1)[1].split("decreases", 1)[0]
    assert "vrep_" in invariant.split(".\n", 1)[0], invariant
    assert "class_ReopenOwner__abs_rep_current_model" in invariant, invariant
    assert "func_ReopenOther_ReadOrRaise" in text
    assert "raises" in text
    if method == "ReadOnlyLoop":
        assert "#perm_this" in invariant
        assert "class_ReopenOwner__abs_model_current" in invariant
        assert "== pre_this" in invariant
fixed = (here / "out/Func_ReopenOwner_NoReopenLoop.fst").read_text()
assert "vrep_" not in fixed.split("invariant exists*", 1)[1].split(".\n", 1)[0]

source = (here / "ReopenLoop.cs").read_text()
source = "using System;\nusing PalLang;\nnamespace PalCSharp.Tests;\n" + source[
    source.index('[Invariant("OwnerSpec.Holds'):
]
for name, method, negative in (
    ("PrivateIdentity", "Loop", source.replace("return i;", "Pal.Assert(hidden == saved);\n        return i;", 1)),
    ("ReadonlyIdentity", "ReadOnlyLoop",
     source[:source.index("public int ReadOnlyLoop")] +
     source[source.index("public int ReadOnlyLoop"):].replace(
         "return i;", "Pal.Assert(hidden == saved);\n        return i;", 1)),
    ("StaleCurrent", "Loop", source.replace(
        "this.Value == Pal.Old(this.Value) + 1", "this.Value == Pal.Old(this.Value)", 1)),
):
    owner = "Negative" + name + "Owner"
    with tempfile.TemporaryDirectory(prefix="pal-reopen-loop-") as temporary:
        directory = Path(temporary)
        fixture = directory / "Negative.cs"
        fixture.write_text(negative.replace("ReopenOwner", owner))
        translated = subprocess.run(
            [compiler, "--reference", str(here / "out"), "-o", temporary, str(fixture)],
            capture_output=True, text=True,
        )
        assert translated.returncode == 0, translated.stdout + translated.stderr
        command = [
            str(root / "tools/run-fstar.sh"), "--include", temporary,
            "--include", str(here / "out"), "--include", str(here / "_cache"),
            "--include", str(root / "pulse/_cache"), "--cache_checked_modules",
            "--cache_dir", temporary, "--already_cached", "*",
        ]
        checked = subprocess.run(command + [str(directory / f"Class_{owner}.fst")],
                                 capture_output=True, text=True)
        assert checked.returncode == 0, checked.stdout + checked.stderr
        checked = subprocess.run(command + [str(directory / f"Func_{owner}_{method}.fst")],
                                 capture_output=True, text=True)
        failure = checked.stdout + checked.stderr
        assert checked.returncode != 0, name + " incorrectly preserved private identity or stale model"
        assert "could not prove" in failure or "Failed to prove" in failure, failure
        assert "Identifier not found" not in failure, failure

print("Reopened loops: current/Old/refined models, actual fractions and raising paths checked; private identity rejected; untouched raw frames fixed")
