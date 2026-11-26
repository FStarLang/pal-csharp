import subprocess
import sys
import tempfile
from pathlib import Path
from urllib.parse import unquote

here = Path(__file__).resolve().parent
root = here.parent.parent
compiler = sys.argv[1]
positive = (here / "out/Func_GhostFieldHolder_ReadThroughLoan.fst").read_text()
loan = positive.split("Let_LeaseProof_Begin.lemma_LeaseProof_Begin", 1)[1].split(
    "Let_LeaseProof_End.lemma_LeaseProof_End", 1
)[0]
assert "Class_CellOwner.class_CellOwner__inv" not in loan
assert "Class_CurrentModelOwner.class_CurrentModelOwner__inv" in loan
assert "GhostOwnedFields.twice" in loan
assert "spec_GhostFieldHolder_Value (reveal pre_this)" in loan
assert "Let_LeaseProof_Keep.lemma_LeaseProof_Keep" in loan
restored = positive.split("Let_LeaseProof_End.lemma_LeaseProof_End", 1)[1]
assert restored.count("Class_CellOwner.class_CellOwner__inv") == 2
assert restored.count("spec_GhostFieldHolder_Total (reveal pre_this)") == 2
assert "drop_" not in positive
distinct = (here / "out/Func_GhostFieldHolder_ReadWithDistinctOwner.fst").read_text()
distinct_loan = distinct.split("Let_LeaseProof_Begin.lemma_LeaseProof_Begin", 1)[1].split(
    "Let_LeaseProof_End.lemma_LeaseProof_End", 1
)[0]
assert "Class_GhostFieldHolder.class_GhostFieldHolder__inv var_distinct" in distinct_loan
assert "Class_CellOwner.class_CellOwner__inv" not in distinct_loan
assert "spec_GhostFieldHolder_Total (reveal pre_this)" not in distinct_loan

source = (here / "GhostOwnedFields.cs").read_text()
source = source.replace('[assembly: IncludePulseFile("GhostOwnedFields.fst")]', "")
source = source[:source.index("public static class GhostFieldSpecs")] + source[
    source.index("public sealed class GhostFieldHolder"):
]
boundary = "LeaseProof.End(value, Pal.Permission());"
assert source.count(boundary) == 2
for name, observation in (
    ("Direct", "child.Value == value.Value"),
    ("Nested", "GhostFieldSpecs.Twice(child.Value) == GhostFieldSpecs.Twice(value.Value)"),
    ("Receiver", "this.Total == value.Value + second.Value"),
    ("Alias", "alias.Total == value.Value + second.Value"),
):
    owner = "Negative" + name + "GhostFieldHolder"
    negative = source.replace("GhostFieldHolder", owner).replace(
        boundary, "Pal.Assert(" + observation + ");\n        " + boundary, 1
    )
    with tempfile.TemporaryDirectory(prefix="pal-ghost-owned-fields-") as temporary:
        directory = Path(temporary)
        fixture = directory / "Negative.cs"
        fixture.write_text(negative)
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
        checked = subprocess.run(command + [str(directory / ("Class_" + owner + ".fst"))],
                                 text=True, capture_output=True)
        assert checked.returncode == 0, checked.stdout + checked.stderr
        target = directory / ("Func_" + owner + "_ReadThroughLoan.fst")
        checked = subprocess.run(command + [str(target)], text=True, capture_output=True)
        failure = " ".join(unquote(checked.stdout + checked.stderr).split())
        assert checked.returncode != 0, name + " observation read a missing owned-field model"
        assert "Cannot prove: Class_CellOwner.class_CellOwner__inv" in failure, failure
        assert "OwnerLease.opened" in failure, failure

with tempfile.TemporaryDirectory(prefix="pal-reassigned-holder-alias-") as temporary:
    fixture = Path(temporary) / "Reassigned.cs"
    fixture.write_text(source.replace("GhostFieldHolder", "ReassignedGhostFieldHolder").replace(
        "ReadThroughLoan()", "ReadThroughLoan(ReassignedGhostFieldHolder replacement)"
    ).replace("var alias = this;", "var alias = this;\n        alias = replacement;"))
    translated = subprocess.run(
        [compiler, "--reference", str(here / "out"), "-o", temporary, str(fixture)],
        text=True, capture_output=True,
    )
    diagnostics = translated.stdout + translated.stderr
    assert translated.returncode != 0, "A reassigned reference reused a stale same-slot alias"
    assert "This assignment target" in diagnostics, diagnostics

print("Owned-field ghosts: selective/nested/inferred/Old/alias captures checked; missing ownership rejected")
