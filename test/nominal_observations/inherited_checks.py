#!/usr/bin/env python3
"""Regressions for view-typed laws and ordinary enumerable loans in replicas."""
from pathlib import Path
import shutil
import subprocess

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
text = (HERE / "Inherited.cs").read_text()
cases = (
    ("inherited-wrong-count", text.replace("public int Count => CountCore;", "public int Count => 1;"),
     "Func_Window_at_Inherited_Count"),
    ("inherited-wrong-order", text.replace("public override IComparer<T> Order => order;",
                                          "public override IComparer<T> Order => source.Order;"),
     "Func_Window_at_Inherited_Comparer"),
    ("inherited-missing-unlend", text, "Func_Window_at_Inherited_Adapt"),
    ("inherited-hidden-order", text.replace("public override IComparer<T> Order => order;",
                                           "public new IComparer<T> Order => order;"), ""),
)
for name, changed, target in cases:
    work = HERE / "obj" / name
    if work.exists():
        shutil.rmtree(work)
    work.mkdir(parents=True)
    (work / "Inherited.cs").write_text(changed)
    out = work / "out"
    run = subprocess.run([ROOT / "src/Pal.Tool/bin/Debug/net10.0/palcs", "-o", out,
                          HERE / "Observations.cs", work / "Inherited.cs"],
                         capture_output=True, text=True)
    if name == "inherited-hidden-order":
        assert run.returncode != 0 and "PALCS0866" in run.stdout + run.stderr, run.stdout + run.stderr
        print("rejected:", name, flush=True)
        continue
    assert run.returncode == 0, run.stdout + run.stderr
    if name == "inherited-missing-unlend":
        path = out / (target + ".fst")
        before = path.read_text()
        lines = before.splitlines(keepends=True)
        removed = [line for line in lines if "Enumerable.unlend " in line]
        assert len(removed) == 1, before
        path.write_text("".join(line for line in lines if line not in removed))
    cache = work / "_cache"
    cache.mkdir()
    for checked in (HERE / "_cache").glob("*.checked"):
        module = checked.name.removesuffix(".checked")
        current, original = out / module, HERE / "out" / module
        if current.exists() and original.exists() and current.read_bytes() == original.read_bytes():
            shutil.copyfile(checked, cache / checked.name)
    run = subprocess.run([ROOT / "tools/run-fstar.sh", "--include", ROOT / "pulse/_cache",
                          "--include", out, "--include", cache, out / (target + ".fst")],
                         capture_output=True, text=True)
    output = run.stdout + run.stderr
    assert run.returncode != 0 and ("Failed to prove" in output or "Cannot prove" in output), output
    print("rejected:", name, flush=True)
