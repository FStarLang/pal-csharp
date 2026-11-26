#!/usr/bin/env python3
"""Demand ordinary/view iterator installation from the active public implementation."""
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
HERE = ROOT / "samples/dotnet-runtime/pal/SortedSet"
GENERIC = ROOT / "samples/dotnet-runtime/src/libraries/System.Collections/src/System/Collections/Generic"
OUT = HERE / "obj/iterator-hit/out"


def main():
    # No source generalization here: the persistent gate must exercise the
    # promoted implementation, and fail if its Exactly restriction returns.
    args = [ROOT / "src/Pal.Tool/bin/Debug/net10.0/palcs", "-o", OUT, "--preview", "--unsafe"]
    args += [arg for name in ("List", "Queue", "Stack")
             for arg in ("--reference", HERE.parent / name / "out")]
    args += [
        GENERIC / "SortedSet.cs",
        *[GENERIC / name for name in
          ("SortedSet.TreeSubSet.cs", "SortedSetEqualityComparer.cs", "SortedDictionary.cs")],
        HERE.parent / "common/GlobalUsings.cs", HERE.parent / "common/Scope.cs",
        *sorted(HERE.glob("*.cs")),
        Path(__file__).with_name("SortedSetIteratorInstallation.cs"),
    ]
    result = subprocess.run(list(map(str, args)), stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT, text=True)
    print("\n".join(line for line in result.stdout.splitlines()
                    if "error" in line.lower() or "module(s)" in line))
    witness = OUT / "Func_TreeSubSet_at_SortedSet_EnumerationProof.fst"
    print(f"View protocol emitted: {witness.is_file()}: {witness}")
    return result.returncode or (0 if witness.is_file() else 1)


if __name__ == "__main__":
    sys.exit(main())
