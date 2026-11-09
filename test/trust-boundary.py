#!/usr/bin/env python3
"""Pin explicitly trusted sources; this is a review tripwire, not a soundness proof."""

import argparse
import hashlib
from pathlib import Path
import re
import sys

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--update", action="store_true", help="accept the reviewed trust inventory")
args = parser.parse_args()
root = Path(__file__).resolve().parent.parent
manifest = root / "doc/trusted-sources.sha256"
sources = []
for path in sorted((root / "pulse").glob("*.fst*")):
    # Interface-only modules may assert arbitrary types without an `assume` keyword.
    # Including comments in this conservative scan can only add review obligations.
    interface_only = path.suffix == ".fsti" and not path.with_suffix(".fst").exists()
    explicit_trust = re.search(r"\bassume\b|\badmit\s*\(", path.read_text())
    if interface_only or explicit_trust:
        sources.append(path)
sources.extend(root / "tools" / name for name in ("fstar-version.txt", "fstar-source.txt"))
expected = "".join(
    f"{hashlib.sha256(path.read_bytes()).hexdigest()}  {path.relative_to(root)}\n"
    for path in sorted(sources)
    if path.exists()
)
if args.update:
    manifest.write_text(expected)
elif not manifest.exists() or manifest.read_text() != expected:
    print("trust-boundary: trusted sources changed; review and run test/trust-boundary.py --update",
          file=sys.stderr)
    sys.exit(1)
else:
    print(f"trust-boundary: OK ({len(expected.splitlines())} pinned sources)")
