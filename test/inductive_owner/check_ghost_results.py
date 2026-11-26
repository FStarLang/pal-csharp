import subprocess
import sys
import tempfile
from pathlib import Path

here = Path(__file__).resolve().parent
root = here.parent.parent
with tempfile.TemporaryDirectory(prefix="pal-ghost-results-") as temporary:
    output = Path(temporary)
    translated = subprocess.run(
        [sys.argv[1], "-o", temporary, str(here / "GhostResultNegative.cs.in")],
        text=True, capture_output=True,
    )
    diagnostics = translated.stdout + translated.stderr
    assert translated.returncode != 0, diagnostics
    assert "error PALCS0504:" in diagnostics, diagnostics
    assert "lemma call in a pure specification expression" in diagnostics, diagnostics
    command = [
        str(root / "tools/run-fstar.sh"), "--cache_checked_modules",
        "--cache_dir", temporary, "--include", temporary,
        "--include", str(root / "pulse/_cache"),
    ]
    for name in ("Class_ProbeCell", "GhostResultNegative", "Let_ProbeProof_Unpack"):
        checked = subprocess.run(
            command + [str(output / (name + ".fst"))], text=True, capture_output=True,
        )
        assert checked.returncode == 0, checked.stdout + checked.stderr
    for name in ("Func_ProbeClient_Leak", "Func_ProbeClient_NamedLeak"):
        checked = subprocess.run(
            command + [str(output / (name + ".fst"))],
            text=True, capture_output=True,
        )
        diagnostics = checked.stdout + checked.stderr
        assert checked.returncode != 0, "A ghost witness leaked into runtime code: " + name
        assert "Expected a total term, but this term has Ghost effect" in diagnostics, diagnostics

client = (here / "out/Func_WitnessClient_Read.fst").read_text()
assert (
    "let record : erased (Class_OwnedCell.class_OwnedCell__raw) = "
    "Let_WitnessProof_UnpackKnown.lemma_WitnessProof_UnpackKnown"
) in client, client
assert "hide (Let_WitnessProof_UnpackKnown" not in client
print("Ghost results: checked resource witnesses; runtime leakage and pure calls rejected")
