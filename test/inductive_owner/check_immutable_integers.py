import subprocess
import sys
import tempfile
from pathlib import Path

here = Path(__file__).resolve().parent
output = here / "out"
for name in ("Once", "Make"):
    code = (output / ("Func_ImmutableIntegers_" + name + ".fst")).read_text()
    assert "let mut var_local" not in code, code
    assert code.count("func_ImmutableIntegers_Observe ") == 2, code
for name in ("ByRef", "Assigned", "Nested", "InCall", "OutCall", "RawScope"):
    code = (output / ("Func_ImmutableIntegers_" + name + ".fst")).read_text()
    assert "let mut var_local" in code, name + " lost its required backing storage"
with tempfile.TemporaryDirectory(prefix="pal-immutable-alias-") as temporary:
    translated = subprocess.run(
        [sys.argv[1], "--unsafe", "-o", temporary, str(here / "ImmutableAlias.cs.in")],
        text=True, capture_output=True,
    )
    diagnostics = translated.stdout + translated.stderr
    assert translated.returncode != 0 and "error PALCS0001:" in diagnostics, diagnostics
    for name in ("ThroughAlias", "Captured", "Address", "ImplicitIn"):
        code = (Path(temporary) / ("Func_ImmutableAlias_" + name + ".fst")).read_text()
        assert "let mut var_local" in code, name + " was incorrectly classified immutable"
print("Immutable integers: once-only initialization; writes, references, captures and raw scopes excluded")
