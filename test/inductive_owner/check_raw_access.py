import subprocess
import tempfile
import sys
from pathlib import Path

here = Path(__file__).resolve().parent
root = here.parent.parent
outputs = {
    name: (here / f"out/Func_RawOwner_{name}.fst").read_text()
    for name in ("Load", "NullableLoad", "Store", "CellStore", "Commit")
}
for name in ("Load", "Store"):
    outputs["Shared" + name] = (here / f"out/Func_RawGeneric_{name}.fst").read_text()
for name, text in outputs.items():
    assert "B.op_Bang" in text, name
    assert "class_RawOwner__inv" not in text, name
    assert "class_RawGeneric__inv" not in text, name
    assert "class_RawOwner__opt" not in text, name
assert "let mut var_owner" in outputs["CellStore"]
assert "fld_state = (RetainedOwner.of_payload var_payload)" in outputs["Commit"]
assert outputs["Store"].count("B.op_Colon_Equals") == 1
assert outputs["Commit"].count("B.op_Colon_Equals") == 1

# Perturb only the generated pre/post resource permissions, retaining the exact
# compiled bodies. This checks that raw access relies on Pulse's real points-to
# obligation, not a compiler-inserted invariant or assumed permission.
cases = []
for name in ("Load", "NullableLoad", "Store", "Commit", "SharedLoad", "SharedStore"):
    lines = outputs[name].splitlines()
    weakened = "\n".join(
        "  requires emp" if line.startswith("  requires ") else
        "  ensures emp" if line.startswith("  ensures ") and not line.endswith("**") else
        "  ensures emp **" if line.startswith("  ensures ") else line
        for line in lines
    )
    cases.append(("Missing" + name, weakened))
for name in ("Store", "Commit", "SharedStore"):
    cases.append(("Fractional" + name, outputs[name].replace("1.0R", "RawAccess.half")))

for name, text in cases:
    module = "NegativeRaw" + name
    text = text.replace(text.splitlines()[0], "module " + module, 1)
    with tempfile.TemporaryDirectory(prefix="pal-raw-access-") as directory:
        fixture = Path(directory) / (module + ".fst")
        fixture.write_text(text)
        checked = subprocess.run(
            [str(root / "tools/run-fstar.sh"), "--include", str(here / "out"),
             "--include", str(here / "_cache"), "--include", str(root / "pulse/_cache"),
             "--already_cached", "*", str(fixture)],
            capture_output=True, text=True,
        )
        output = checked.stdout + checked.stderr
        assert checked.returncode != 0, name + " unsoundly accepted"
        assert "Cannot prove" in output or "Failed to prove" in output, output
        assert "Identifier" not in output and "Syntax error" not in output, output

source = (here / "RawShared.cs").read_text().replace(
    '[assembly: IncludePulseFile("RawShared.fst")]', "")
for name, negative in (
    ("NonShared", source.replace(
        "public sealed class RawReverse<X, Y> : RawGeneric<Y, X> { }",
        "public sealed class RawReverse<X, Y> : RawGeneric<Y, X> { private int extra; }")),
    ("Mismatched", source.replace(
        "Store([Plain] RawReverse<B, A> owner, A next)",
        "Store([Plain] RawReverse<A, B> owner, A next)")),
):
    with tempfile.TemporaryDirectory(prefix="pal-raw-shared-") as directory:
        fixture = Path(directory) / "Negative.cs"
        fixture.write_text(negative)
        checked = subprocess.run(
            [sys.argv[1], "--reference", str(here / "out"), "-o", directory, str(fixture)],
            capture_output=True, text=True,
        )
        output = checked.stdout + checked.stderr
        assert checked.returncode != 0, name + " incorrectly accepted"
        assert "PALCS0523" in output or "CS0029" in output or "CS1503" in output, output

print("Explicit raw modeled owners: Value/Cell, nullable, erased fields and generic shared representations checked; nine permission and two representation negatives rejected")
