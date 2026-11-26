#!/usr/bin/env python3
"""Check real generic SpecOp clients, including a dishonest element argument."""
from pathlib import Path
import shutil
import subprocess

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
source = (HERE / "GenericValues.cs").read_text()
for label, text in (
    ("positive", source),
    ("wrong-element", source.replace(
        "Check(Pal.Contents(items), 2, 0)",
        "Check(Pal.Contents(items), 3, 0)")),
):
    work = HERE / "obj/generic-values" / label
    if work.exists():
        shutil.rmtree(work)
    work.mkdir(parents=True)
    path = work / "GenericValues.cs"
    path.write_text(text)
    out, cache = work / "out", work / "_cache"
    cache.mkdir()
    subprocess.run([ROOT / "src/Pal.Tool/bin/Debug/net10.0/palcs",
                    "-o", out, path], check=True)
    modules = ["GenericSpecValues", "Func_GenericValues_Variable",
               "Func_GenericValues_Wide", "Func_GenericValues_Literal"]
    for module in modules:
        result = subprocess.run([
            ROOT / "tools/run-fstar.sh", "--force", "--z3refresh", "--z3rlimit", "10",
            "--cache_checked_modules", "--cache_dir", cache,
            "--include", out, "--include", cache,
            "--include", ROOT / "pulse/_cache",
            "--already_cached", "Prims,FStar,Pulse,Pulse.Main,Pulse.Nolib,Pulse.Class,Pulse.Lib,PulseCore",
            out / (module + ".fst")
        ], stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
        if label == "wrong-element" and module == "Func_GenericValues_Literal":
            if result.returncode == 0 or "Failed to prove" not in result.stdout:
                raise SystemExit(result.stdout or "wrong element unexpectedly verified")
            if (cache / (module + ".fst.checked")).exists():
                raise SystemExit("negative produced a checked artifact")
            print("wrong element: type-correct call rejected by the lemma precondition")
        elif result.returncode:
            raise SystemExit(result.stdout)
    if label == "positive":
        print("literal Int32, variable Int32, Int64 and mathematical index: freshly verified")
