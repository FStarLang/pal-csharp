#!/usr/bin/env python3
"""Negative laws/ownership checks for the checked resource-producing protocol."""
from pathlib import Path
import re
import shutil
import subprocess

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
BASE = HERE / "obj/iterator"
TEXT = (HERE / "SequenceProtocol.cs").read_text()
CASES = (
    ("exception-domain", TEXT.replace("RequireValid(true);", "RequireValid(false);"),
     "Func_SequenceProtocolClient_AnyValid"),
    ("loop-exception-domain", TEXT.replace("RequireValid(true) &&", "RequireValid(false) &&"),
     "Func_SequenceProtocolClient_CheckedLoop"),
    ("next", TEXT.replace("index = 1; return true;", "index = 1; return false;"),
     "Func_Stream_Cursor_MoveNext"),
    ("current", TEXT.replace("public T Current => owner.item;", "public T Current => default(T)!;"),
     "Func_Stream_Cursor_Current"),
    ("fact", TEXT.replace('Ensures("@this.Elements.Length == 1 && @this.Kind")',
                          'Ensures("@this.Elements.Length == 2 && @this.Kind")'),
     "Func_Stream_Trace"),
    ("factory-domain", TEXT.replace(
        '[Ensures("ReferenceEquals(Result.owner, @this) && Result.index == 0")]',
        '[Requires("Pal.Same(@this.Elements[0], default(T))")]\n'
        '    [Ensures("ReferenceEquals(Result.owner, @this) && Result.index == 0")]'),
     "Func_SequenceProtocolClient_Hit"),
    ("dispose-state", TEXT.replace("public void Dispose() { }", "public void Dispose() { index = 0; }"),
     "Func_SequenceProtocolClient_Hit"),
    ("premature-current", TEXT.replace("bool moved = cursor.MoveNext();",
                                      "T early = cursor.Current; bool moved = cursor.MoveNext();"),
     "Func_SequenceProtocolClient_Consume"),
    ("two-live-cursors", TEXT.replace("bool moved = cursor.MoveNext();",
                                     "var second = source.GetEnumerator(); bool moved = cursor.MoveNext();"),
     "Func_SequenceProtocolClient_Consume"),
    ("cursor-alias", TEXT.replace("bool moved = cursor.MoveNext();",
                                 "var alias = cursor; bool moved = alias.MoveNext();"),
     "Func_SequenceProtocolClient_Consume"),
)


def run(args):
    return subprocess.run(list(map(str, args)), stdout=subprocess.PIPE,
                          stderr=subprocess.STDOUT, text=True)


def main():
    assert (BASE / "_cache/.verified").exists(), "Run the positive iterator gate first"
    partial = (BASE / "out/Func_SequenceProtocolClient_Partial.fst").read_text()
    assert "Enumerable.Iterator.release" in partial
    assert "Enumerable.Iterator.dispose" not in partial
    assert "Seq.length" in (BASE / "out/NominalFacts_Stream.fst").read_text()
    print("checked: partial traversal releases without an invented Dispose", flush=True)
    for name, source, target in CASES:
        assert source != TEXT, name
        work = HERE / "obj" / ("iterator-negative-" + name)
        if work.exists():
            shutil.rmtree(work)
        work.mkdir(parents=True)
        (work / "SequenceProtocol.cs").write_text(source)
        translated = run([ROOT / "src/Pal.Tool/bin/Debug/net10.0/palcs",
                          "-o", work / "out", HERE / "Observations.cs", work / "SequenceProtocol.cs"])
        if translated.returncode:
            assert name in ("two-live-cursors", "cursor-alias"), translated.stdout
            assert "PALCS0866" in translated.stdout, translated.stdout
            print("rejected by frontend:", name, flush=True)
            continue
        cache = work / "_cache"
        cache.mkdir()
        for checked in (BASE / "_cache").glob("*.checked"):
            filename = checked.name.removesuffix(".checked")
            before, after = BASE / "out" / filename, work / "out" / filename
            if before.is_file() and after.is_file() and before.read_bytes() == after.read_bytes():
                shutil.copyfile(checked, cache / checked.name)
        checked = run(["make", "-C", HERE, "PHASE=verify", f"OUT={(work / 'out').relative_to(HERE)}",
                       f"CACHE_DIR={cache.relative_to(HERE)}", f"EXTRA_INCLUDES={ROOT / 'pulse/_cache'}",
                       cache.relative_to(HERE) / f"{target}.fst.checked", "-j4"])
        assert checked.returncode != 0, (name, checked.stdout)
        assert re.search(r"Failed to prove|Could not|Cannot (match|prove)", checked.stdout), (name, checked.stdout)
        print("rejected by verification:", name, flush=True)

    # Removing the release implementation's deallocation must leave an
    # unconsumed heap resource, not silently turn reclamation into a leak.
    work = HERE / "obj/iterator-negative-release"
    if work.exists():
        shutil.rmtree(work)
    shutil.copytree(BASE / "out", work / "out")
    shutil.copytree(BASE / "_cache", work / "_cache")
    target = "Nominal_SequenceProtocolClient_Hit___pal_nominal_snapshot0"
    implementation = work / "out" / f"{target}.fst"
    text = implementation.read_text()
    assert text.count("B.free actual.cell;") == 1
    implementation.write_text(text.replace("B.free actual.cell;", "();"))
    (work / "_cache" / f"{target}.fst.checked").unlink()
    (work / "_cache/.depend").unlink(missing_ok=True)
    checked = run(["make", "-C", HERE, "PHASE=verify", f"OUT={(work / 'out').relative_to(HERE)}",
                   f"CACHE_DIR={(work / '_cache').relative_to(HERE)}",
                   f"EXTRA_INCLUDES={ROOT / 'pulse/_cache'}",
                   (work / "_cache").relative_to(HERE) / f"{target}.fst.checked", "-j4"])
    assert checked.returncode != 0, checked.stdout
    assert "resource" in checked.stdout.lower(), checked.stdout
    assert "error PALCS0600" in checked.stdout, checked.stdout
    print("rejected by verification: incomplete cursor reclamation", flush=True)


if __name__ == "__main__":
    main()
