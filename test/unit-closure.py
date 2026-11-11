#!/usr/bin/env python3
"""Print what verify.mk needs to know about the units a harness references (R36.1).

Each argument is a referenced unit's output directory. Its `unit.json` names the unit's
own references, so the closure is followed transitively and printed dependencies first:

  --dirs     the output directories, one per line
  --modules  the modules they emit, comma-separated, as F*'s `--already_cached` takes them
"""

import json
import os
import sys


def closure(dirs):
    seen = []

    def visit(d):
        d = os.path.abspath(d)
        if d in seen:
            return
        with open(os.path.join(d, "unit.json")) as f:
            manifest = json.load(f)
        for r in manifest["references"]:
            visit(r)
        seen.append(d)
        units[d] = manifest

    units = {}
    for d in dirs:
        visit(d)
    return [(d, units[d]) for d in seen]


def main():
    mode, dirs = sys.argv[1], sys.argv[2:]
    units = closure(dirs)
    if mode == "--dirs":
        print("\n".join(d for d, _ in units))
    elif mode == "--modules":
        print(",".join(m for _, u in units for m in u["modules"]))
    else:
        sys.exit(f"unit-closure.py: unknown mode {mode}")


if __name__ == "__main__":
    main()
