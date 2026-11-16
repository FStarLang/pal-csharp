#!/usr/bin/env python3
"""Print what verify.mk needs to know about the units a harness references (R36.1).

Each argument is a referenced unit's output directory. Its `unit.json` names the unit's
own references, so the closure is followed transitively and printed dependencies first:

  --dirs     the output directories, one per line
  --modules  the modules they emit, comma-separated, as F*'s `--already_cached` takes them
  --check CACHE  require checked dependencies and remove old local copies from CACHE
"""

import json
import os
import sys


def closure(dirs):
    seen = []
    visiting = set()

    def visit(d):
        d = os.path.abspath(d)
        if d in seen:
            return
        if d in visiting:
            sys.exit(f"unit-closure.py: reference cycle at {d}")
        visiting.add(d)
        with open(os.path.join(d, "unit.json")) as f:
            manifest = json.load(f)
        for r in manifest["references"]:
            visit(r)
        seen.append(d)
        visiting.remove(d)
        units[d] = manifest

    units = {}
    for d in dirs:
        visit(d)
    return [(d, units[d]) for d in seen]


def main():
    mode, dirs = sys.argv[1], sys.argv[2:]
    if mode == "--check":
        cache, *dirs = dirs
    units = closure(dirs)
    if mode == "--dirs":
        print("\n".join(d for d, _ in units))
    elif mode == "--modules":
        print(",".join(m for _, u in units for m in u["modules"]))
    elif mode == "--check":
        for directory, unit in units:
            for module in unit["modules"]:
                if not os.path.isfile(os.path.join(directory, module + ".fst")):
                    sys.exit(f"unit-closure.py: {directory}/{module}.fst is missing; translate its unit first")
                for extension in (".fst", ".fsti"):
                    source = os.path.join(directory, module + extension)
                    if not os.path.isfile(source):
                        continue
                    filename = module + extension + ".checked"
                    checked = os.path.join(os.path.dirname(directory), "_cache", filename)
                    if not os.path.isfile(checked) or os.path.getmtime(source) > os.path.getmtime(checked):
                        sys.exit(f"unit-closure.py: {checked} is missing or stale; verify its unit first")
                    local = os.path.join(cache, filename)
                    if os.path.isfile(local):
                        os.unlink(local)
    else:
        sys.exit(f"unit-closure.py: unknown mode {mode}")


if __name__ == "__main__":
    main()
