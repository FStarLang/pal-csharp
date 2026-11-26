#!/usr/bin/env python3
"""Isolated, force-checked C# dependency chains for projected enumerable loans."""
from pathlib import Path
import shutil
import subprocess
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
PALCS = ROOT / "src/Pal.Tool/bin/Debug/net10.0/palcs"
FSTAR = ROOT / "tools/run-fstar.sh"
SOURCE = (HERE / "Projected.cs").read_text()
BASE = ["TranslationErrors", "Struct_ParcelModel", "Class_Parcel"]
BASE += ["Func_Parcel_" + m for m in
         ("_ctor", "Count", "CopyTo", "GetEnumerator", "ChangeRevision")]
METHODS = ["Func_Projected_" + m for m in ("Test", "Mixed", "PatternEarly")]
CLIENTS = ["Func_Projected_Successful", "Func_Projected_Failed", "Func_Projected_Generic"]


def check(label, source, failures=(), diagnostic=False):
    work = HERE / "obj" / label
    if work.exists():
        shutil.rmtree(work)
    out, cache = work / "out", work / "_cache"
    out.mkdir(parents=True)
    cache.mkdir()
    cs = work / "Projected.cs"
    cs.write_text(source)
    translated = subprocess.run([PALCS, "-o", out, cs], text=True,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    if diagnostic:
        if translated.returncode == 0 or "PALCS0866" not in translated.stdout:
            raise SystemExit(translated.stdout)
        print(f"{label}: mutating observation rejected with PALCS0866")
        return
    if translated.returncode:
        raise SystemExit(translated.stdout)
    modules = BASE + METHODS + ([] if label == "hidden-mutation" else CLIENTS)
    for module in modules:
        result = subprocess.run(
            [FSTAR, "--force", "--z3refresh", "--z3rlimit", "10",
             "--cache_checked_modules", "--cache_dir", cache,
             "--include", out, "--include", cache,
             "--include", ROOT / "pulse", "--include", ROOT / "pulse/_cache",
             "--already_cached", "Prims,FStar,Pulse,Pulse.Main,Pulse.Nolib,Pulse.Class,Pulse.Lib,PulseCore",
             out / (module + ".fst")],
            text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        reject = module in failures
        if (result.returncode != 0) != reject:
            raise SystemExit(f"{label}/{module}: unexpected outcome\n{result.stdout}")
        if reject:
            if (not any(message in result.stdout for message in ("Failed to prove", "Cannot prove:")) or
                    (cache / (module + ".fst.checked")).exists()):
                raise SystemExit(result.stdout)
            if module in CLIENTS:
                lines = [i for i, line in enumerate(
                    (out / (module + ".fst")).read_text().splitlines(), 1)
                    if "Seq.lemma_eq_intro" in line]
                line = lines[1 if label == "bad-enumeration" else 0]
                if f"{module}.fst({line}," not in result.stdout:
                    raise SystemExit(f"not the expected correspondence obligation:\n{result.stdout}")
            print(f"{label}: {module}: expected proof failure")
        else:
            print(f"{label}: {module}: verified")

def check_frozen_model():
    work = HERE / "obj" / "frozen-model"
    work.mkdir(exist_ok=True)
    source = (HERE / "ProjectedFacts.fst").read_text().replace(
        "module ProjectedFacts", "module FrozenModel").replace("[@@expect_failure]", "")
    path = work / "FrozenModel.fst"
    path.write_text(source)
    line = next(i for i, s in enumerate(source.splitlines(), 1) if "C.close_match" in s)
    result = subprocess.run(
        [FSTAR, "--force", "--z3refresh", "--z3rlimit", "10",
         "--include", ROOT / "pulse", "--include", ROOT / "pulse/_cache",
         "--already_cached", "Prims,FStar,Pulse,Pulse.Main,Pulse.Nolib,Pulse.Class,Pulse.Lib,PulseCore", path],
        text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    if result.returncode == 0 or f"FrozenModel.fst({line}," not in result.stdout:
        raise SystemExit(f"Frozen model did not fail at close_match:\n{result.stdout}")
    print("frozen-model: full-permission write verifies; restoring the changed model fails at close_match")


if sys.argv[1:] == ["positive"]:
    check("fresh", SOURCE)
elif sys.argv[1:] == ["negative"]:
    bad_enum = SOURCE.replace(
        '[Ensures("Pal.Yielded<T>().Length == 1 && Pal.Same(Pal.Yielded<T>()[0], @this.Elements[0])")]',
        '[Ensures("Pal.Yielded<T>().Length == 0")]').replace(
        "yield return _items[0];", "if (_items.Length == 0) { yield return _items[0]; }")
    check("bad-enumeration", bad_enum, CLIENTS)
    bad_copy = SOURCE.replace(
        '[Ensures("Pal.Contents(array) == Pal.Splice(Pal.Old(Pal.Contents(array)), index, index + @this.Elements.Length, @this.Elements)")]',
        '[Ensures("true")]').replace(
        "Array.Copy(_items, 0, array, index, _items.Length);", "{}")
    # Change the expression-bodied method into an ordinary empty method.
    bad_copy = bad_copy.replace("public void CopyTo(T[] array, int index) =>\n        {}",
                               "public void CopyTo(T[] array, int index) {}")
    check("bad-copy", bad_copy, CLIENTS)
    bad_projection = SOURCE.replace(
        "[Spec, EnumerationModel] public Seq<T> Elements => Model.Values;",
        "[Spec] public Seq<T> Elements => Model.Values;\n"
        "    [Spec, EnumerationModel] public Seq<T> Enumeration => Pal.EmptySeq<T>();")
    check("bad-projection", bad_projection, CLIENTS)
    hidden = SOURCE.replace("// Nested early return:", "candidate.ChangeRevision();\n            // Nested early return:")
    check("hidden-mutation", hidden, ["Func_Projected_Test"])
    mutating_count = SOURCE.replace("public int Count => _items.Length;",
                                   "public int Count { get { _revision = 9; return _items.Length; } }")
    check("mutating-count", mutating_count, diagnostic=True)
    check_frozen_model()
elif sys.argv[1:] == ["frozen"]:
    check_frozen_model()
else:
    raise SystemExit("usage: checks.py positive|negative|frozen")
