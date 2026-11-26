#!/usr/bin/env python3
"""Reproduce the generated call without editing compiler output or contracts.

Run `make translate SOURCES='Observations.cs ClosedViewCall.cs'
OUT=obj/closed-view/out` first. Generated diagnostic variants live under obj/.
No verifier options affecting contracts, fuel, or resource limits are added.
"""
import argparse
from pathlib import Path
import subprocess


HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
parser = argparse.ArgumentParser()
parser.add_argument("mode", choices=("baseline", "explicit"))
parser.add_argument("--trace", action="store_true")
parser.add_argument("--padding", type=int, default=0)
parser.add_argument("--fstar", type=Path, default=ROOT / "tools/run-fstar.sh")
args = parser.parse_args()

source = HERE / "obj/closed-view/out"
cache = HERE / "obj/closed-view/_cache"
text = (source / "Func_ClosedViewCall_Run.fst").read_text()
name = "ClosedViewDiagnostic_" + args.mode
if args.padding:
    name += "_pad" + str(args.padding)
text = text.replace("module Func_ClosedViewCall_Run", "module " + name, 1)
if args.mode == "explicit":
    start = "  let t4 = func_Empty_at_Packet_CompareObserved "
    line = next(line for line in text.splitlines() if line.startswith(start))
    assert line.endswith(" false);")
    explicit = line[:-1] + (
        " #(hide vcall_owner) #1.0R #(hide vkept_record_5)"
        " #vnominal_model_3 #1.0R #(hide t11);"
    )
    # Model/API arguments are already explicit in the generated call.
    # Also instantiate the generic observation projections and selectors.
    for member in ("contents", "scalar", "select_length", "select_scalar"):
        symbol = "Pulse.Lib.CSharp.Enumerable.Observation." + member
        explicit = explicit.replace(symbol + " ", "(" + symbol
            + " #ty_T #(Pulse.Lib.CSharp.Order.comparer ty_T)) ")
    text = text.replace(line,
        "  with vcall_owner. assert (Class_Packet.class_Packet__inv"
        " var_receiver #1.0R vcall_owner);\n" + explicit, 1)
if args.padding:
    marker = "  let t4 = func_Empty_at_Packet_CompareObserved "
    assert text.count(marker) == 1
    text = text.replace(marker, "".join(
        f"  let diagnostic_padding_{i} = true;\n" for i in range(args.padding)
    ) + marker, 1)

out = HERE / "obj/call-diagnostic"
out.mkdir(parents=True, exist_ok=True)
path = out / (name + ".fst")
path.write_text(text)
cmd = [str(args.fstar.resolve()), "--force"]
for directory in (ROOT / "pulse", ROOT / "pulse/_cache", source, cache, out):
    cmd += ["--include", str(directory)]
cmd += ["--print_implicits", "--print_full_names", "--print_bound_var_types"]
if args.trace:
    cmd += ["--debug", "refl_tc_callbacks"]
cmd.append(str(path))
result = subprocess.run(cmd, cwd=ROOT)
raise SystemExit(result.returncode)
