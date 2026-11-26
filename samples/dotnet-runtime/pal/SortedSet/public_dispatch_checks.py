#!/usr/bin/env python3
"""Translation probes of actual public bodies, not alternate implementations.

Inputs are isolated under obj/public-dispatch. Failed translation is reported,
not accepted as evidence that a public-method implementation has been proved.
"""
from pathlib import Path
import re
import shutil
import subprocess
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
GENERIC = ROOT / "samples/dotnet-runtime/src/libraries/System.Collections/src/System/Collections/Generic"
PALCS = ROOT / "src/Pal.Tool/bin/Debug/net10.0/palcs"

def run(mode, verify=True):
    if mode not in ("view-iterator", "exact-view", "general-public"):
        raise SystemExit("usage: public_dispatch_checks.py view-iterator|exact-view|general-public")
    work = HERE / "obj/public-dispatch" / mode
    work.mkdir(parents=True, exist_ok=True)
    source = (GENERIC / "SortedSet.cs").read_text()
    (work / "SortedSet.cs").write_text(source)
    body = {
        "view-iterator": """var set = SortedSetPublicRegression.CreateSet();
            var view = set.GetViewBetween(2, 5);
            var iterator = view.GetEnumerator();
            bool moved = iterator.MoveNext();
            if (moved) { int item = iterator.Current; }
            iterator.Dispose();
            return moved;""",
        "exact-view": """var set = SortedSetPublicRegression.CreateSet();
            var view = set.GetViewBetween(2, 5);
            var other = new SortedSet<int>();
            other.Add(9);
            Pal.Assert(other.SpecItems.Length == 1 && other.SpecItems[0] == 9);
            SortedSetCount.RangeMisses(set.SpecComparer, 2, 5, true, true,
                set.SpecItems, other.SpecItems, 0);
            return view.SetEquals(other);""",
        "general-public": """return SortedSetPublicRegression.ViewSetEqualsListFalse();"""
    }[mode]
    postcondition = "true" if mode == "view-iterator" else "!Result"
    (work / "PublicDispatchProbe.cs").write_text(
        "using PalLang;\nnamespace System.Collections.Generic {\n"
        "internal static class PublicDispatchProbe {\n"
        f'[Ensures("{postcondition}")] internal static bool Run() {{\n'
        + body + "\n} } }\n")
    refs = [HERE.parent / n / "out" for n in ("List", "Queue", "Stack", "HashSet")]
    sources = [work / "SortedSet.cs"] + [
        GENERIC / name for name in
        ("SortedSet.TreeSubSet.cs", "SortedSetEqualityComparer.cs", "SortedDictionary.cs")]
    sources += [HERE.parent / "common/GlobalUsings.cs", HERE.parent / "common/Scope.cs",
                *sorted(HERE.glob("*.cs")), work / "PublicDispatchProbe.cs"]
    result = subprocess.run(list(map(str, [
        PALCS, "-o", work / "out", "--preview", "--unsafe",
        *[arg for path in refs for arg in ("--reference", path)], *sources
    ])), stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    diagnostics = [line for line in result.stdout.splitlines()
                   if re.search(r"\berror (?:PALCS|CS)\d+", line)]
    print(f"{mode}: {len(diagnostics)} translation errors; inputs: {work}")
    print("\n".join(diagnostics[:18]))
    if not result.returncode:
        if verify:
            cache = work / "_cache"
            if cache.exists():
                shutil.rmtree(cache)
            names = ["Func_PublicDispatchProbe_Run"]
            if mode == "view-iterator":
                names += [
                    "Func_SortedSet_GetEnumerator",
                    "Func_SortedSet_Enumerator_MoveNext",
                    "Func_SortedSet_Enumerator_Current",
                    "Func_SortedSet_Enumerator_Dispose",
                ]
            targets = [cache / f"{name}.fst.checked" for name in names]
            checked = subprocess.run(list(map(str, [
                "make", "-C", HERE, "PHASE=verify", f"OUT={(work / 'out').relative_to(HERE)}",
                f"CACHE_DIR={cache.relative_to(HERE)}", "REFERENCES_BUILT=1",
                f"EXTRA_INCLUDES=. {ROOT / 'pulse/_cache'}",
                *[target.relative_to(HERE) for target in targets], "-j8"])),
                stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
            for line in checked.stdout.splitlines():
                if not line.startswith(str(ROOT / "tools/run-fstar.sh")):
                    print(line)
            if checked.returncode or not all(target.is_file() for target in targets):
                print(f"Actual {mode} dependency chain NOT verified.")
                return checked.returncode or 1
            print(f"Actual {mode} dependency chain verified.")
        else:
            print("Translation passed; implementation verification is still required.")
    elif not diagnostics:
        print(result.stdout)
    return result.returncode


if __name__ == "__main__":
    raise SystemExit(run(sys.argv[1] if len(sys.argv) == 2 else ""))
