"""Reject false identity claims, checking actual F* proof failure diagnostics."""
import json
import pathlib
import subprocess

root = pathlib.Path(__file__).resolve().parents[2]
for name in ("NegativeOverride.fst", "NegativeEquatable.fst", "NegativeReinterpretation.fst", "NegativeFactory.fst"):
    result = subprocess.run(
        [
            str(root / "tools/run-fstar.sh"),
            "--message_format", "json",
            "--already_cached", "Prims,FStar,Pulse,Pulse.Main,Pulse.Nolib,Pulse.Class,Pulse.Lib,PulseCore",
            "--include", str(root / "pulse/_cache"),
            "--include", "_cache",
            "--include", "out",
            name,
        ],
        text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
        timeout=120,
    )
    diagnostics = []
    for line in result.stdout.splitlines():
        try:
            diagnostics.append(json.loads(line))
        except json.JSONDecodeError:
            pass
    if result.returncode == 0 or not any(
        d.get("level") == "Error"
        and d.get("number") == 19
        and "could not prove" in json.dumps(d).lower()
        for d in diagnostics
    ):
        raise RuntimeError(f"{name}: expected proof rejection\n{result.stdout}")
    print(f"OK: rejected {name}")
