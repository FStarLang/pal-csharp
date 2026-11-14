import subprocess
import sys
import tempfile
from pathlib import Path

here = Path(__file__).resolve().parent
root = here.parent.parent
compiler = sys.argv[1]
for fixture in ("UnsupportedOwningTuple", "SwitchJoinNegative"):
    with tempfile.TemporaryDirectory(prefix="pal-tuples-joins-") as temporary:
        output = Path(temporary)
        translated = subprocess.run(
            [compiler, "-o", temporary, str(here / (fixture + ".cs.in"))],
            text=True, capture_output=True,
        )
        diagnostics = translated.stdout + translated.stderr
        assert translated.returncode != 0, diagnostics
        if fixture == "UnsupportedOwningTuple":
            assert diagnostics.count("error PALCS0001:") == 2, diagnostics
            assert "return type" in diagnostics and "parameter type" in diagnostics, diagnostics
            assert not (output / "Func_OwningTuples_Duplicate.fst").exists()
            assert all("Struct_ValueTuple" not in path.read_text() for path in output.glob("*.fst"))
        else:
            assert "error PALCS0752:" in diagnostics, diagnostics
            source = output / "Func_SwitchJoinNegative_FalseJoin.fst"
            assert "ensures exists*" in source.read_text(), source.read_text()
            checked = subprocess.run(
                [str(root / "tools/run-fstar.sh"), "--include", temporary,
                 "--include", str(root / "pulse/_cache"), str(source)],
                text=True, capture_output=True,
            )
            failure = checked.stdout + checked.stderr
            assert checked.returncode != 0, "The false switch-contained join was accepted"
            assert "Assertion failed" in failure, failure

joined = (here / "out/Func_MixedSwitch_Joined.fst").read_text()
assert "if (var_choose)\n" in joined and "ensures exists*" in joined, joined
join_post = joined.split("if (var_choose)\n", 1)[1].split("{", 1)[0]
assert "OwnerCells.held" in join_post and "pure (" in join_post, join_post
for name in ("Pair", "NullablePair", "Empty", "GhostSequence"):
    generated = (here / ("out/Func_PlainTuples_" + name + ".fst")).read_text()
    assert "Struct_ValueTuple" not in generated, generated
    assert "class_CallbackCell__opt" in generated, generated
print("Plain tuples and switch joins: positive proofs, emission, and negative checks passed")
