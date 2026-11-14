import subprocess
import sys
import tempfile
from pathlib import Path

here = Path(__file__).resolve().parent
root = here.parent.parent


def translate(source, output):
    return subprocess.run(
        [sys.argv[1], "-o", str(output), str(source)], text=True, capture_output=True
    )


with tempfile.TemporaryDirectory(prefix="pal-conditional-ghost-") as temporary:
    output = Path(temporary)
    result = translate(here / "ConditionalGhostNegative.cs.in", output)
    assert result.returncode == 0, result.stdout + result.stderr
    command = [
        str(root / "tools/run-fstar.sh"),
        "--cache_checked_modules", "--cache_dir", temporary,
        "--include", temporary, "--include", str(root / "pulse/_cache"),
    ]
    checked = subprocess.run(
        command + [str(output / "Class_InformativeOwner.fst")],
        text=True, capture_output=True,
    )
    assert checked.returncode == 0, checked.stdout + checked.stderr
    for module in ("Func_InformativeOwner_BadUpdate", "Func_InformativeOwner_BadLocalUpdate",
                   "Func_ConditionalGhostLeak_Leak"):
        checked = subprocess.run(
            command + [str(output / (module + ".fst"))],
            text=True, capture_output=True,
        )
        diagnostics = checked.stdout + checked.stderr
        assert checked.returncode != 0, "Accepted informative ghost operation: " + module
        assert "error" in diagnostics.lower(), diagnostics
        if module.endswith("Update"):
            assert "erased" in diagnostics, diagnostics
        else:
            assert "Ghost" in diagnostics, diagnostics

    invalid = {
        "recapture": """
            Ghost<int> snapshot = default;
            Pal.Capture(ref snapshot, 1);
            Pal.Capture(ref snapshot, 2);
        """,
        "self-reference": """
            Ghost<int> snapshot = default;
            Pal.Capture(ref snapshot, snapshot.Value);
        """,
        "nonadjacent": """
            Ghost<int> snapshot = default;
            Pal.Assert(true);
            Pal.Capture(ref snapshot, 1);
        """,
        "ordinary-field": "Pal.UpdateGhost(ref value, 1);",
        "ordinary-local": "int local = 0; Pal.UpdateGhost(ref local, 1);",
        "effectful-capture": """
            Ghost<int> snapshot = default;
            Pal.Capture(ref snapshot, value++);
        """,
    }
    for name, body in invalid.items():
        source = output / (name + ".cs")
        source.write_text(
            "using PalLang; public sealed class Probe { private int value; "
            "[Model] private int Model => value; public void Bad() {" + body + "} }"
        )
        translated = translate(source, output / name)
        diagnostics = translated.stdout + translated.stderr
        assert translated.returncode != 0, "Accepted invalid ghost operation: " + name
        assert "ghost capture" in diagnostics or "ghost update" in diagnostics, diagnostics

print("Conditional ghost operations: immutable captures, erased writes, and no runtime leaks")
