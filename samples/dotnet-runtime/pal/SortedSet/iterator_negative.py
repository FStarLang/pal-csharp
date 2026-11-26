#!/usr/bin/env python3
"""The actual ordinary iterator still needs its stale-version exception guard.

Run after public_dispatch_checks.py view-iterator checks both iterator chains.
The positive MoveNext cache is deliberately unavailable to the mutant.
"""
from pathlib import Path
import re
import shutil
import subprocess

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
GENERIC = ROOT / "samples/dotnet-runtime/src/libraries/System.Collections/src/System/Collections/Generic"
work = HERE / "obj/iterator-no-version-check"
if work.exists():
    shutil.rmtree(work)
work.mkdir(parents=True)
text = (GENERIC / "SortedSet.cs").read_text()
start = text.index("            public bool MoveNext()")
end = text.index("            public void Dispose()", start)
body, changed = re.subn(
    r"                if \(_version != _tree.version\)\s*\{\s*"
    r"throw new InvalidOperationException\(SR.InvalidOperation_EnumFailedVersion\);\s*\}",
    "", text[start:end], count=1)
if changed != 1:
    raise SystemExit("missing actual MoveNext version guard")
path = work / "SortedSet.cs"
path.write_text(text[:start] + body + text[end:])
sources = [path, *[GENERIC / n for n in (
    "SortedSet.TreeSubSet.cs", "SortedSetEqualityComparer.cs", "SortedDictionary.cs")],
    HERE.parent / "common/GlobalUsings.cs", HERE.parent / "common/Scope.cs", *sorted(HERE.glob("*.cs"))]
refs = [HERE.parent / n / "out" for n in ("List", "Queue", "Stack", "HashSet")]
subprocess.run([ROOT / "src/Pal.Tool/bin/Debug/net10.0/palcs", "-o", work / "out",
    "--preview", "--unsafe", *[str(v) for p in refs for v in ("--reference", p)], *sources], check=True)
target = "Func_SortedSet_Enumerator_MoveNext.fst"
positive = HERE / "obj/public-dispatch/view-iterator/_cache"
if not (positive / (target + ".checked")).is_file():
    raise SystemExit("check the ordinary positive chain first")
shutil.copytree(positive, work / "deps", ignore=shutil.ignore_patterns(target + ".checked"))
cache = work / "_cache"
cache.mkdir()
includes = [work / "out", work / "deps", cache, HERE, ROOT / "pulse/_cache", ROOT / "pulse"]
for name in ("List", "Queue", "Stack", "HashSet", "HashCommon", "common"):
    includes += [HERE.parent / name / "_cache", HERE.parent / name / "out"]
result = subprocess.run([ROOT / "tools/run-fstar.sh", "--force", "--z3refresh", "--z3rlimit", "10",
    "--cache_checked_modules", "--cache_dir", cache,
    "--already_cached", "Prims,FStar,Pulse,Pulse.Main,Pulse.Nolib,Pulse.Class,Pulse.Lib,PulseCore",
    *[str(v) for p in includes for v in ("--include", p)], work / "out" / target],
    stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
if not result.returncode or (cache / (target + ".checked")).exists() or "Failed to prove" not in result.stdout:
    raise SystemExit(result.stdout or "removed version guard unexpectedly verified")
print("Actual ordinary MoveNext without its version guard: expected implementation-proof failure.")
