import re
from pathlib import Path

here = Path(__file__).resolve().parent
for name, callee in (
    ("Nullable", "func_PlainReturns_Observe"),
    ("NonNull", "func_PlainTuples_Observe"),
    ("EffectfulReturn", "func_PlainReturns_Observe"),
):
    generated = (here / ("out/Func_PlainReturns_" + name + ".fst")).read_text()
    assert generated.count(callee + " ty_T var_cell var_calls") == 1, generated
    assert generated.count("func_PlainCleanupOwner__ctor") == 1, generated
    assert "drop_ (Class_PlainCleanupOwner.class_PlainCleanupOwner__inv" in generated, generated
    returned = re.search(r"\n  (t\d+)\n}\s*$", generated)
    assert returned, generated
    assert not re.search(r"let " + returned[1] + r" = t\d+;", generated), generated
print("Plain return binders: one evaluation, opaque ownership, and cleanup retained")
