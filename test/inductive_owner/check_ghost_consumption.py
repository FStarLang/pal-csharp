import subprocess
import sys
import tempfile
from pathlib import Path

here = Path(__file__).resolve().parent
compiler = sys.argv[1]
for suffix, lemma in (("CellOwner", "Retain"), ("int", "RetainVoid")):
    text = (here / f"out/Func_RetainingHolder__ctor_{suffix}.fst").read_text()
    call = f"Let_RetainedProof_{lemma}.lemma_RetainedProof_{lemma} var_owner"
    assert call in text, text
    assert "var_alias" not in text, text
    assert "drop_" not in text, text
    assert "RetainedOwner.model_value var_owner" not in text, text
    assert "RetainedOwner.model_value " in text, text
    after = text.split(call, 1)[1]
    assert "Class_CellOwner.class_CellOwner__inv var_owner" not in after, after

source = (here / "RetainedOwner.cs").read_text()
source = source[source.index('[Invariant("RetainedSpec.StateHeld'): ]
source = source.replace("#endif", "")
source = "using PalLang;\nnamespace PalCSharp.Tests;\n" + source
boundary = "payload = RetainedSpec.State(retained.Value);"
assert source.count(boundary) == 2
for form in (0, 1):
    for name, use in (
        ("OwnerRead", "owner.Read();"),
        ("AliasRead", "alias.Read();"),
        ("OwnerModel", "Pal.Assert(owner.Value == value.Value);"),
        ("AliasModel", "Pal.Assert(alias.Value == value.Value);"),
        ("AliasRaw", "Pal.Assert(RetainedSpec.Describes(retained.Value, alias, value.Value));"),
        ("ConsumeTwice", "RetainedProof.RetainVoid(alias, value, retained);"),
    ):
        parts = source.split(boundary)
        parts[form + 1] = "\n" + use + parts[form + 1]
        negative = boundary.join(parts).replace("RetainingHolder", f"Negative{form}{name}")
        with tempfile.TemporaryDirectory(prefix="pal-ghost-consume-") as temporary:
            fixture = Path(temporary) / "Negative.cs"
            fixture.write_text(negative)
            result = subprocess.run(
                [compiler, "--reference", str(here / "out"), "-o", temporary, str(fixture)],
                text=True, capture_output=True,
            )
            diagnostic = result.stdout + result.stderr
            assert result.returncode != 0, f"{form}/{name}: accepted consumed owner"
            assert "PALCS0550" in diagnostic, diagnostic
            assert "cannot be used after it is passed" in diagnostic, diagnostic

print("Ghost consumption: result/void retention, raw aliases, model observations and 12 use-after-consume checks passed")
