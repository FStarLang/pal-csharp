#!/usr/bin/env python3
"""Reject unsupported nominal evidence and broken checked miss implementations."""
from pathlib import Path
import shutil
import subprocess

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
MISS = (HERE / "Misses.cs").read_text()
PROTOCOL = (HERE / "SequenceProtocol.cs").read_text()
CASES = (
    ("miss-unknown-runtime",
     MISS.replace("Ordinary<T>(T value, IComparer<T> comparer)",
                  "Ordinary<T>(T value, IComparer<T> comparer, Cargo<T> source)")
         .replace("        var source = new Cargo<T>(value);\n", "", 1),
     PROTOCOL, "", "PALCS0866"),
    ("miss-missing-enumeration-model",
     MISS.replace("[Spec, EnumerationModel]", "[Spec]"),
     PROTOCOL, "", "PALCS0866"),
    ("miss-missing-protocol", MISS,
     PROTOCOL.replace("[EnumerationProtocol, Frac", "[Frac"),
     "", "PALCS0866"),
    ("miss-wrong-count", MISS.replace("Count => 1", "Count => 2"),
     PROTOCOL, "Func_Cargo_Count", ""),
    ("miss-wrong-enumeration",
     MISS.replace("yield return item;", "yield return item; yield return item;"),
     PROTOCOL, "Func_Cargo_GetEnumerator", ""),
    ("miss-wrong-current-sequence", MISS,
     PROTOCOL.replace("CurrentItems => index == 1", "CurrentItems => index == 0"),
     "Func_Stream_Cursor_MoveNext", ""),
    ("miss-missing-restore", MISS, PROTOCOL, "Func_MissClient_Ordinary", ""),
    ("miss-double-pack", MISS, PROTOCOL, "Func_MissClient_Ordinary", ""),
)

for name, miss, protocol, target, diagnostic in CASES:
    work = HERE / "obj" / name
    if work.exists():
        shutil.rmtree(work)
    work.mkdir(parents=True)
    sources = []
    for file, text in (("Observations.cs", (HERE / "Observations.cs").read_text()),
                       ("Misses.cs", miss), ("SequenceProtocol.cs", protocol)):
        path = work / file
        path.write_text(text)
        sources.append(path)
    out, cache = work / "out", work / "_cache"
    translated = subprocess.run(
        [ROOT / "src/Pal.Tool/bin/Debug/net10.0/palcs", "-o", out, *sources],
        capture_output=True, text=True, timeout=90)
    output = translated.stdout + translated.stderr
    if diagnostic:
        assert translated.returncode != 0 and diagnostic in output, (name, output)
        print("rejected:", name, flush=True)
        continue
    assert translated.returncode == 0, (name, output)
    path = out / (target + ".fst")
    if name in ("miss-missing-restore", "miss-double-pack"):
        lines = path.read_text().splitlines(keepends=True)
        needle = ("Capability.unpack " if name == "miss-missing-restore"
                  else "Capability.pack ")
        index = next(i for i, line in enumerate(lines) if needle in line)
        lines[index] = "" if name == "miss-missing-restore" else lines[index] * 2
        path.write_text("".join(lines))
    cache.mkdir()
    baseline = HERE / "obj/disjoint"
    for checked in (baseline / "_cache").glob("*.checked"):
        module = checked.name.removesuffix(".checked")
        old, new = baseline / "out" / module, out / module
        if old.exists() and new.exists() and old.read_bytes() == new.read_bytes():
            shutil.copyfile(checked, cache / checked.name)
    command = [ROOT / "tools/run-fstar.sh", "--force",
               "--include", ROOT / "pulse/_cache",
               "--include", out, "--include", cache, path]
    run = subprocess.run(command, capture_output=True, text=True, timeout=90)
    output = run.stdout + run.stderr
    assert run.returncode == 1 and any(s in output for s in (
        "Failed to prove", "Cannot prove", "Could not prove", "Could not match"
    )), (name, output)
    print("rejected:", name, flush=True)
