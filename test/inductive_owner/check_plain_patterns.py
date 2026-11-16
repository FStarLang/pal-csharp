import subprocess
import sys
import tempfile
from pathlib import Path

here = Path(__file__).resolve().parent
root = here.parent.parent
for source, code in (
    (here / "UnsupportedPlainPatterns.cs.in", "PALCS0001"),
    (root / "test/diagnostics/cases/JoinNullLocal.cs", "PALCS0754"),
):
    with tempfile.TemporaryDirectory(prefix="pal-plain-patterns-") as output:
        translated = subprocess.run([sys.argv[1], "-o", output, str(source)],
                                    text=True, capture_output=True)
        diagnostics = translated.stdout + translated.stderr
        assert translated.returncode != 0 and ("error " + code + ":") in diagnostics, diagnostics
        if source.name == "UnsupportedPlainPatterns.cs.in":
            assert diagnostics.count("error PALCS0001:") == 3, diagnostics

with tempfile.TemporaryDirectory(prefix="pal-plain-join-resource-") as output:
    translated = subprocess.run(
        [sys.argv[1], "-o", output, str(here / "PlainJoinResourceNegative.cs.in")],
        text=True, capture_output=True)
    assert translated.returncode == 0, translated.stdout + translated.stderr
    command = [
        str(root / "tools/run-fstar.sh"), "--cache_checked_modules", "--cache_dir", output,
        "--include", output, "--include", str(root / "pulse/_cache"),
    ]
    checked = subprocess.run(command + [str(Path(output) / "Class_JoinCell.fst")],
                             text=True, capture_output=True)
    assert checked.returncode == 0, checked.stdout + checked.stderr
    for name in ("Forge", "Terminal", "Loop"):
        source = Path(output) / ("Func_PlainJoinResourceNegative_" + name + ".fst")
        assert "ensures " in source.read_text().split("{", 1)[1], source.read_text()
        checked = subprocess.run(command + [str(source)], text=True, capture_output=True)
        diagnostics = checked.stdout + checked.stderr
        assert checked.returncode != 0, "An impossible final join was accepted: " + name
        if name == "Forge":
            assert "pts_to" in diagnostics and "Cannot prove:" in diagnostics, diagnostics
        else:
            assert "Assertion failed" in diagnostics, diagnostics

for name in ("Observed", "Joined"):
    generated = (here / ("out/Func_PlainPatterns_" + name + ".fst")).read_text()
    assert generated.count("func_PlainLocals_Observe var_cell var_calls") == 1, generated
    assert "if (true)" not in generated, generated
joined = (here / "out/Func_PlainPatterns_Joined.fst").read_text()
assert "ensures exists*" in joined, joined
print("Plain patterns: null checks, one capture, ghost scope, checked joins, owning-local rejection")
