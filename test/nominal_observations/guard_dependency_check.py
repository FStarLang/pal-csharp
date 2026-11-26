#!/usr/bin/env python3
"""Check the real public List client and reject its guard-free dependency chain."""
from pathlib import Path
import runpy
import shutil
import subprocess

ROOT = Path(__file__).resolve().parents[2]
HERE = ROOT / "samples/dotnet-runtime/pal/SortedSet"
GENERIC = ROOT / "samples/dotnet-runtime/src/libraries/System.Collections/src/System/Collections/Generic"
BASE = HERE / "obj/public-dispatch/general-public"
WORK = HERE / "obj/nominal-guard-negative"
CLIENT = "Func_PublicDispatchProbe_Run"
HELPER = "Func_TreeSubSet_at_SortedSet_CheckUniqueAndUnfoundElements"


def run(args):
    return subprocess.run(list(map(str, args)), stdout=subprocess.PIPE,
                          stderr=subprocess.STDOUT, text=True)


def verify(work, *names):
    return run(["make", "-C", HERE, "PHASE=verify",
                f"OUT={(work / 'out').relative_to(HERE)}",
                f"CACHE_DIR={(work / '_cache').relative_to(HERE)}",
                "REFERENCES_BUILT=1", f"EXTRA_INCLUDES=. {ROOT / 'pulse/_cache'}",
                *[str((work / "_cache").relative_to(HERE) / f"{n}.fst.checked")
                  for n in names], "-j6"])


def main():
    probe = runpy.run_path(str(HERE / "public_dispatch_checks.py"))
    assert probe["run"]("general-public", verify=False) == 0
    positive = verify(BASE, CLIENT, HELPER)
    assert positive.returncode == 0, positive.stdout
    print("verified: guarded public List false-result client and helper closure", flush=True)

    if WORK.exists():
        shutil.rmtree(WORK)
    WORK.mkdir(parents=True)
    text = (BASE / "SortedSet.cs").read_text()
    guard = "int index = IsWithinRange(item) ? InternalIndexOf(item) : -1;"
    assert text.count(guard) == 1
    (WORK / "SortedSet.cs").write_text(text.replace(guard, "int index = InternalIndexOf(item);"))
    shutil.copyfile(BASE / "PublicDispatchProbe.cs", WORK / "PublicDispatchProbe.cs")
    translated = run([
        ROOT / "src/Pal.Tool/bin/Debug/net10.0/palcs", "-o", WORK / "out", "--preview", "--unsafe",
        *[arg for n in ("List", "Queue", "Stack")
          for arg in ("--reference", HERE.parent / n / "out")],
        WORK / "SortedSet.cs",
        *[GENERIC / n for n in ("SortedSet.TreeSubSet.cs", "SortedSetEqualityComparer.cs", "SortedDictionary.cs")],
        HERE.parent / "common/GlobalUsings.cs", HERE.parent / "common/Scope.cs",
        *sorted(HERE.glob("*.cs")), WORK / "PublicDispatchProbe.cs"])
    assert translated.returncode == 0, translated.stdout
    cache = WORK / "_cache"
    cache.mkdir()
    # Reuse only byte-identical modules. The changed implementation has no
    # checked artifact, and make must check it before accepting any dependents.
    for checked in (BASE / "_cache").glob("*.checked"):
        name = checked.name.removesuffix(".checked")
        original, changed = BASE / "out" / name, WORK / "out" / name
        if original.is_file() and changed.is_file() and original.read_bytes() == changed.read_bytes():
            shutil.copyfile(checked, cache / checked.name)
    assert not (cache / f"{HELPER}.fst.checked").exists()
    negative = verify(WORK, CLIENT, HELPER)
    assert negative.returncode != 0, negative.stdout
    assert f"{HELPER}.fst.checked] Error" in negative.stdout, negative.stdout
    assert "Failed to prove" in negative.stdout, negative.stdout
    print("rejected: guard-free view helper implementation in full public dependency chain", flush=True)

    # Deliberately demonstrate why checking only a caller is insufficient.
    # F* checks this module using imported contracts, not those implementations.
    (cache / f"{CLIENT}.fst.checked").unlink(missing_ok=True)
    includes = [ROOT / "pulse", ROOT / "pulse/_cache", WORK / "out", cache, HERE]
    includes += [HERE.parent / unit / sub for unit in ("common", "List", "Queue", "Stack")
                 for sub in ("out", "_cache")]
    caller = run([ROOT / "tools/run-fstar.sh",
                  "--already_cached", "Prims,FStar,Pulse",
                  *[arg for directory in includes for arg in ("--include", directory)],
                  WORK / "out" / f"{CLIENT}.fst"])
    assert caller.returncode == 0, caller.stdout
    print("verified in isolation only: caller still follows the unproved helper contract", flush=True)
    print("The guard-free program is NOT verified.", flush=True)


if __name__ == "__main__":
    main()
