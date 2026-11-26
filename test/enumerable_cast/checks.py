#!/usr/bin/env python3
"""Fresh dependency-chain checks, never mutating the active C# or proof cache."""
from pathlib import Path
import shutil
import subprocess
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
PALCS = ROOT / "src/Pal.Tool/bin/Debug/net10.0/palcs"
FSTAR = ROOT / "tools/run-fstar.sh"
SOURCE = (HERE / "EnumerableCast.cs").read_text()


def check(label, source, reject_clients):
    work = HERE / "obj" / label
    if work.exists():
        shutil.rmtree(work)
    out, cache = work / "out", work / "_cache"
    out.mkdir(parents=True)
    cache.mkdir()
    cs = work / "EnumerableCast.cs"
    cs.write_text(source)
    subprocess.run([PALCS, "-o", out, cs], check=True)
    modules = ["TranslationErrors", "Class_Envelope", "Class_Packet"]
    modules += [f"Func_{c}_{m}" for c in ("Envelope", "Packet")
                for m in ("_ctor", "Count", "CopyTo", "GetEnumerator")]
    modules += ["Func_EnumerableCast_IsPacket"]
    modules += ["Func_EnumerableCast_Successful", "Func_EnumerableCast_Failed"]
    for module in modules:
        command = [FSTAR, "--force", "--z3refresh", "--z3rlimit", "10",
                   "--cache_checked_modules", "--cache_dir", cache,
                   "--include", out, "--include", cache,
                   "--include", ROOT / "pulse", "--include", ROOT / "pulse/_cache",
                   "--already_cached", "Prims,FStar,Pulse,Pulse.Main,Pulse.Nolib,Pulse.Class,Pulse.Lib,PulseCore",
                   out / (module + ".fst")]
        result = subprocess.run(command, text=True, stdout=subprocess.PIPE,
                                stderr=subprocess.STDOUT)
        expected_failure = reject_clients and module in (
            "Func_EnumerableCast_Successful", "Func_EnumerableCast_Failed")
        if (result.returncode != 0) != expected_failure:
            print(result.stdout)
            raise SystemExit(f"{label}: unexpected result for {module}")
        if expected_failure:
            correspondence = [i for i, line in enumerate(
                (out / (module + ".fst")).read_text().splitlines(), 1)
                if "Seq.lemma_eq_intro" in line]
            failed_line = correspondence[-1 if label == "bad-enumeration" else 0]
            if (f"{module}.fst({failed_line}," not in result.stdout or
                    "Failed to prove" not in result.stdout or
                    (cache / (module + ".fst.checked")).exists()):
                print(result.stdout)
                raise SystemExit(f"{label}: failure was not a correspondence proof")
            print(f"{label}: {module}: expected correspondence proof failure")
        else:
            print(f"{label}: {module}: verified")


if sys.argv[1:] == ["positive"]:
    check("fresh", SOURCE, False)
elif sys.argv[1:] == ["negative"]:
    # Each implementation still verifies against its weaker, honest contract.
    # Only the adapter's independently checked correspondence must fail.
    bad_enumeration = SOURCE.replace(
        '[Ensures("@this.Items.Length == 1 && Pal.Yielded<int>().Length == 1 && Pal.Yielded<int>()[0] == @this.Items[0]")]',
        '[Ensures("Pal.Yielded<int>().Length == 1 && Pal.Yielded<int>()[0] == 42")]'
    ).replace("yield return _items[0];", "yield return 42;")
    assert bad_enumeration != SOURCE
    check("bad-enumeration", bad_enumeration, True)
    bad_copy = SOURCE.replace(
        '[Ensures("Pal.Contents(array) == Pal.Splice(Pal.Old(Pal.Contents(array)), index, index + @this.Items.Length, @this.Items)")]',
        '[Ensures("true")]'
    ).replace("Array.Copy(_items, 0, array, index, _items.Length);",
              "array[index] = 42;").replace(
        '[Requires("index >= 0 && index + @this.Items.Length <= Pal.Contents(array).Length")]',
        '[Requires("index >= 0 && index < Pal.Contents(array).Length")]')
    assert bad_copy != SOURCE
    check("bad-copy", bad_copy, True)
else:
    raise SystemExit("usage: checks.py positive|negative")
