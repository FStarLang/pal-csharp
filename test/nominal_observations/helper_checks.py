#!/usr/bin/env python3
"""Checked helper specialization and linear snapshot-forwarding regressions."""
from pathlib import Path
import shutil
import subprocess

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
TEXT = (HERE / "Observations.cs").read_text()
BODY = "return Comparer == other.Comparer || Comparer == other.Comparer;"
CASES = (
    ("helper-wrong-body", TEXT.replace(BODY, "return false;"),
     "Func_Packet_SameOrder__nominal_other", ""),
    ("helper-view-wrong-body", TEXT.replace(BODY, "return false;"),
     "Func_Empty_at_Packet_SameOrder__nominal_other", ""),
    ("helper-original-domain", TEXT.replace("other.Items.Length >= 0", "other.Items.Length > 1"),
     "Func_Packet_CompareObserved", ""),
    ("helper-field-escape", TEXT.replace(BODY, "return other.order == order;"), "", "PALCS0866"),
    ("helper-virtual-dispatch", TEXT.replace("private bool SameOrder", "protected virtual bool SameOrder"),
     "", "PALCS0866"),
    ("helper-pointer-escape", TEXT.replace(BODY, "return ReferenceEquals(other, this);"), "", "PALCS0866"),
    ("helper-missing-match", TEXT, "Func_Packet_SameOrder__nominal_other", ""),
    ("helper-missing-restore", TEXT, "Func_Packet_CompareObserved", ""),
    ("helper-double-forward", TEXT, "Func_Packet_CompareObserved", ""),
)

for name, text, target, diagnostic in CASES:
    work = HERE / "obj" / name
    if work.exists():
        shutil.rmtree(work)
    work.mkdir(parents=True)
    (work / "Observations.cs").write_text(text)
    out, cache = work / "out", work / "_cache"
    translated = subprocess.run([ROOT / "src/Pal.Tool/bin/Debug/net10.0/palcs", "-o", out,
                                 work / "Observations.cs"], capture_output=True, text=True)
    output = translated.stdout + translated.stderr
    if diagnostic:
        assert translated.returncode != 0 and diagnostic in output, (name, output)
        print("rejected:", name, flush=True)
        continue
    assert translated.returncode == 0, (name, output)
    path = out / (target + ".fst")
    generated = path.read_text()
    if name == "helper-missing-match":
        needle = "(Pulse.Lib.CSharp.Capability.supports (reveal descriptor_other))"
        assert needle in generated
        path.write_text(generated.replace(needle, "True"))
    if name == "helper-missing-restore":
        lines = generated.splitlines(keepends=True)
        assert any("Capability.restore_snapshot " in line for line in lines)
        path.write_text("".join(line for line in lines if "Capability.restore_snapshot " not in line))
    if name == "helper-double-forward":
        lines = generated.splitlines(keepends=True)
        assert any("Capability.forward_snapshot " in line for line in lines)
        path.write_text("".join(line + line if "Capability.forward_snapshot " in line else line for line in lines))
    cache.mkdir()
    for checked in (HERE / "_cache").glob("*.checked"):
        module = checked.name.removesuffix(".checked")
        old, new = HERE / "out" / module, out / module
        if old.exists() and new.exists() and old.read_bytes() == new.read_bytes():
            shutil.copyfile(checked, cache / checked.name)
    command = [ROOT / "tools/run-fstar.sh", "--include", ROOT / "pulse/_cache",
               "--include", out, "--include", cache]
    if name == "helper-original-domain":
        for module in ("Func_Packet_SameOrder__nominal_other",):
            run = subprocess.run([*command, "--cache_checked_modules", "--cache_dir", cache,
                                  out / (module + ".fst")], capture_output=True, text=True)
            assert run.returncode == 0, run.stdout + run.stderr
    run = subprocess.run([*command, path], capture_output=True, text=True)
    output = run.stdout + run.stderr
    assert run.returncode != 0 and any(s in output for s in
        ("Failed to prove", "Cannot prove", "Could not prove", "Could not match")), (name, output)
    print("rejected:", name, flush=True)
