#!/usr/bin/env python3
"""Freshness regression gate, with an explicit historical-collision mode.

The class-free cases need only checked generic support under pulse/_cache.
The original generated consumer cases additionally need obj/closed-view/out.
"""
import argparse
from pathlib import Path
import subprocess

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
CACHE = HERE / "obj/call-diagnostic/_cache"
CACHE.mkdir(parents=True, exist_ok=True)
parser = argparse.ArgumentParser()
parser.add_argument("--generated", action="store_true")
parser.add_argument("--fstar", type=Path, default=ROOT / "tools/run-fstar.sh")
parser.add_argument("--expect-collision", action="store_true",
                    help="require the historical error from an unpatched verifier")
args = parser.parse_args()


def check(module, expected):
    command = [
        "timeout", "--kill-after=5s", "90s", str(args.fstar.resolve()),
        "--force", "--cache_checked_modules", "--cache_dir", str(CACHE),
    ]
    includes = [ROOT / "pulse", ROOT / "pulse/_cache", HERE, CACHE]
    if args.generated:
        includes += [HERE / "obj/closed-view/out", HERE / "obj/closed-view/_cache"]
    for path in includes:
        command += ["--include", str(path)]
    command.append(str(HERE / (module + ".fst")))
    result = subprocess.run(command, cwd=ROOT, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    if expected == "verified":
        ok = result.returncode == 0
    else:
        # A timeout or an unrelated failed proof is NOT the reproduced error.
        ok = (result.returncode == 1
              and "Ill-typed term" in result.stdout
              and "Expected type Type" in result.stdout
              and "Pulse.Lib.CSharp.Enumerable.Observation.model" in result.stdout)
    print(f"{module}: {expected if ok else 'UNEXPECTED RESULT'}")
    print(result.stdout, end="")
    if not ok:
        raise SystemExit(1)


check("DependentCall.Capability", "verified")
concrete = "known type error" if args.expect_collision else "verified"
check("DependentCall.CapabilityConcrete", concrete)
check("DependentCall.CapabilityLocal", concrete)
if args.generated:
    check("ClosedViewCore", "verified")
    check("ClosedViewCall.Parameterized", concrete)
    check("ClosedViewCall.Local", concrete)
