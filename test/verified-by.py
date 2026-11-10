#!/usr/bin/env python3
"""Pick the generated modules a harness may take as verified by another harness.

A harness that translates sources another harness also verifies (the SortedSet harness
includes List.cs, Queue.cs and Stack.cs) need not discharge their proof obligations twice.
A module of this harness is *assumed* when it is byte-identical to a module of an owner
harness and so is every module of this harness it transitively depends on: F* then sees
the same text in the same context, and the owner harness proves it. Anything else, such
as a module whose enum literals or callee contracts differ in this harness, is verified
as usual.

An owner must not itself assume modules (it would make trust circular), so a harness
named as an owner may not set VERIFIED_BY.

Writes a makefile fragment: `ASSUMED := <modules>`, and for each assumed module a rule
making its `.checked` depend on the owner's copies, so that an owner-side change re-runs
the selection and the check.
"""

import argparse
import re
import sys
from pathlib import Path

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--out", required=True, help="this harness's generated-module directory")
parser.add_argument("--cache", required=True, help="this harness's cache directory")
parser.add_argument("--depend", required=True, help="F*'s --dep full output for this harness")
parser.add_argument("owners", nargs="*", metavar="DIR=OUT",
                    help="an owner harness directory and where its translation was written")
args = parser.parse_args()

out = Path(args.out)
owners = []
for arg in args.owners:
    d, o = (Path(x) for x in arg.split("=", 1))
    mk = (d / "Makefile").read_text() if (d / "Makefile").exists() else ""
    if re.search(r"^\s*VERIFIED_BY\b", mk, re.M):
        sys.exit(f"verified-by: {d} sets VERIFIED_BY itself; owners must verify everything")
    owners.append((d, o))

# Direct dependencies between this harness's own modules, from the `.checked` rules.
local = {p.stem for p in out.glob("*.fst")}
deps = {m: set() for m in local}
target = None
checked = re.compile(r"(?:^|/)([^/\s]+)\.fst\.checked$")
for line in Path(args.depend).read_text().splitlines():
    if not line.strip():
        target = None
        continue
    if not line.startswith(("\t", " ")) and line.rstrip().endswith((":", ": \\")):
        m = checked.search(line.split(":")[0].strip())
        target = m.group(1) if m and m.group(1) in local else None
        continue
    if target is None:
        continue
    for tok in line.replace("\\", " ").split():
        m = checked.search(tok)
        if m and m.group(1) in local and m.group(1) != target:
            deps[target].add(m.group(1))

def closure(m):
    seen, todo = set(), [m]
    while todo:
        x = todo.pop()
        if x not in seen:
            seen.add(x)
            todo.extend(deps.get(x, ()))
    return seen

def same(m, owner_out):
    theirs = owner_out / f"{m}.fst"
    return theirs.exists() and theirs.read_bytes() == (out / f"{m}.fst").read_bytes()

assumed = {}
for m in sorted(local):
    # This harness's own translation errors are reported here, whatever an owner's are.
    if m == "TranslationErrors":
        continue
    for d, o in owners:
        c = closure(m)
        if all(same(x, o) for x in c):
            assumed[m] = (d, o, sorted(c))
            break

print(f"ASSUMED := {' '.join(assumed)}")
for m, (d, o, c) in assumed.items():
    print(f"ASSUMED_BY_{m} := {d}")
    print(f"{args.cache}/{m}.fst.checked: {' '.join(str(o / f'{x}.fst') for x in c)}")
