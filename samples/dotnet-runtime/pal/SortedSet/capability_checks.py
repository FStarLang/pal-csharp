#!/usr/bin/env python3
"""Isolated checks of the implemented capability prerequisites, not SetEquals."""
from pathlib import Path
import re
import shutil
import subprocess
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
PALCS = ROOT / "src/Pal.Tool/bin/Debug/net10.0/palcs"
FSTAR = ROOT / "tools/run-fstar.sh"
GENERIC = ROOT / "samples/dotnet-runtime/src/libraries/System.Collections/src/System/Collections/Generic"
LIST = ROOT / "samples/dotnet-runtime/src/libraries/System.Private.CoreLib/src/System/Collections/Generic/List.cs"
REF = HERE / "obj/capability-references"
WORK = HERE / "obj/capability"
CACHE = HERE / "obj/capability-fresh/_cache"
COMMON = HERE.parent / "common"


def run(args):
    subprocess.run(list(map(str, args)), check=True)


def translate_list(source, out):
    run([PALCS, "-o", out, "--reference", COMMON / "out", source,
         COMMON / "GlobalUsings.cs", COMMON / "Scope.cs"])
    (out / ".stamp").touch()


def fresh():
    REF.mkdir(parents=True, exist_ok=True)
    shutil.copy2(LIST, REF / "List.cs")
    translate_list(REF / "List.cs", REF / "out")
    run(["make", "-C", HERE.parent / "List", "PHASE=verify",
         f"OUT={REF / 'out'}", f"CACHE_DIR={REF / '_cache'}",
         f"EXTRA_INCLUDES={ROOT / 'pulse/_cache'}", "REFERENCES_BUILT=1",
         "_verify", "-j10"])
    sources = [GENERIC / n for n in (
        "SortedSet.cs", "SortedSet.TreeSubSet.cs", "SortedSetEqualityComparer.cs", "SortedDictionary.cs")]
    sources += [COMMON / "GlobalUsings.cs", COMMON / "Scope.cs", *sorted(HERE.glob("*.cs"))]
    refs = [REF / "out", HERE.parent / "Queue/out", HERE.parent / "Stack/out", HERE.parent / "HashSet/out"]
    run([PALCS, "-o", WORK / "out", "--preview", "--unsafe",
         *[v for p in refs for v in ("--reference", p)], *sources])
    shutil.copy2(HERE / "SortedSetCapability.fst", WORK / "out/SortedSetCapability.fst")
    if CACHE.exists():
        shutil.rmtree(CACHE)
    targets = ["SortedSetCapability", "Func_SortedSetCapabilityRegression_StaticView"]
    run(["make", "-C", HERE, "PHASE=verify", "OUT=obj/capability/out",
         "CACHE_DIR=obj/capability-fresh/_cache", "REFERENCES_BUILT=1",
         "REFERENCES=obj/capability-references ../Queue ../Stack ../HashSet",
         f"EXTRA_INCLUDES=. {ROOT / 'pulse/_cache'}",
         *[f"obj/capability-fresh/_cache/{n}.fst.checked" for n in targets], "-j10"])
    for name in targets:
        if not (CACHE / f"{name}.fst.checked").is_file():
            raise SystemExit(f"missing checked artifact: {name}")
    print("actual view capability and static-client dependency closure verified")


def negative_list():
    work = HERE / "obj/capability-list-negative"
    if work.exists():
        shutil.rmtree(work)
    work.mkdir(parents=True)
    source, count = re.subn(
        r"if \(_version != _list\._version\)\s*\{\s*"
        r"ThrowHelper\.ThrowInvalidOperationException_InvalidOperation_EnumFailedVersion\(\);\s*\}",
        "", LIST.read_text(), count=1)
    if count != 1:
        raise SystemExit("did not locate the actual List.MoveNext version check")
    path = work / "List.cs"
    path.write_text(source)
    translate_list(path, work / "out")
    target = "Func_List_Enumerator_MoveNext"
    # Never expose the active positive target cache to the negative verifier.
    shutil.copytree(REF / "_cache", work / "deps",
                    ignore=shutil.ignore_patterns(target + ".fst.checked"))
    (work / "_cache").mkdir()
    includes = [work / "out", work / "_cache", work / "deps",
                ROOT / "pulse", ROOT / "pulse/_cache", COMMON / "out", COMMON / "_cache"]
    result = subprocess.run(list(map(str, [
        FSTAR, "--force", "--z3refresh", "--z3rlimit", "10",
        "--cache_checked_modules", "--cache_dir", work / "_cache",
        "--already_cached", "Prims,FStar,Pulse,Pulse.Main,Pulse.Nolib,Pulse.Class,Pulse.Lib,PulseCore",
        *[v for p in includes for v in ("--include", p)],
        work / "out" / (target + ".fst")])),
        stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    if result.returncode == 0 or "Failed to prove" not in result.stdout:
        raise SystemExit(result.stdout or "removed List version check unexpectedly verified")
    if (work / "_cache" / (target + ".fst.checked")).exists():
        raise SystemExit("negative target produced a checked artifact")
    print("actual List.MoveNext without its version check: expected proof failure")


if sys.argv[1:] == ["fresh"]:
    fresh()
elif sys.argv[1:] == ["negative-list"]:
    negative_list()
else:
    raise SystemExit("usage: capability_checks.py fresh | negative-list")
