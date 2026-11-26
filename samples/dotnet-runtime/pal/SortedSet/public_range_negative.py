#!/usr/bin/env python3
"""Check the List-backed public client, then remove the actual range guard.

The negative checks the implementation that the public client depends on,
without making its positive checked artifact available to F*.
"""
from pathlib import Path
import shutil
import subprocess

import public_dispatch_checks as public

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
TARGET = "Func_TreeSubSet_at_SortedSet_CheckUniqueAndUnfoundElements.fst"


def run():
    result = public.run("general-public")
    if result:
        return result
    positive = HERE / "obj/public-dispatch/general-public"
    if not (positive / "_cache" / (TARGET + ".checked")).is_file():
        raise SystemExit("the positive client closure did not check the affected implementation")
    work = HERE / "obj/public-dispatch/no-range-guard"
    if work.exists():
        shutil.rmtree(work)
    work.mkdir(parents=True)
    source = (positive / "SortedSet.cs").read_text()
    guard = "int index = IsWithinRange(item) ? InternalIndexOf(item) : -1;"
    if source.count(guard) != 1:
        raise SystemExit("expected exactly one actual counting-loop range guard")
    (work / "SortedSet.cs").write_text(source.replace(guard, "int index = InternalIndexOf(item);"))
    shutil.copyfile(positive / "PublicDispatchProbe.cs", work / "PublicDispatchProbe.cs")
    sources = [work / "SortedSet.cs", *[public.GENERIC / name for name in (
        "SortedSet.TreeSubSet.cs", "SortedSetEqualityComparer.cs", "SortedDictionary.cs")],
        HERE.parent / "common/GlobalUsings.cs", HERE.parent / "common/Scope.cs",
        *sorted(HERE.glob("*.cs")), work / "PublicDispatchProbe.cs"]
    refs = [HERE.parent / name / "out" for name in ("List", "Queue", "Stack", "HashSet")]
    subprocess.run([public.PALCS, "-o", work / "out", "--preview", "--unsafe",
        *[str(value) for path in refs for value in ("--reference", path)], *sources], check=True)
    shutil.copytree(positive / "_cache", work / "deps",
        ignore=shutil.ignore_patterns("*CheckUniqueAndUnfoundElements.fst.checked",
                                     "*SetEquals.fst.checked", "Func_PublicDispatchProbe_Run.fst.checked",
                                     "Func_SortedSetPublicRegression_ViewSetEqualsListFalse.fst.checked"))
    cache = work / "_cache"
    cache.mkdir()
    includes = [work / "out", work / "deps", cache, HERE, ROOT / "pulse/_cache", ROOT / "pulse"]
    for name in ("List", "Queue", "Stack", "HashSet", "HashCommon", "common"):
        includes += [HERE.parent / name / "_cache", HERE.parent / name / "out"]
    result = subprocess.run([ROOT / "tools/run-fstar.sh", "--force", "--z3refresh",
        "--cache_checked_modules", "--cache_dir", cache,
        "--already_cached", "Prims,FStar,Pulse,Pulse.Main,Pulse.Nolib,Pulse.Class,Pulse.Lib,PulseCore",
        *[str(value) for path in includes for value in ("--include", path)], work / "out" / TARGET],
        stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    (work / "verification.log").write_text(result.stdout)
    if (not result.returncode or (cache / (TARGET + ".checked")).exists()
            or "Failed to prove" not in result.stdout or TARGET not in result.stdout):
        raise SystemExit(result.stdout or "unguarded counting implementation unexpectedly verified")
    print("Public SetEquals(List) client and guarded dependency chain verified; "
          "removing the range guard causes the required implementation-proof failure.")
    print(f"Negative proof diagnostics: {work / 'verification.log'}")
    return 0


if __name__ == "__main__":
    raise SystemExit(run())
