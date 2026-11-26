#!/usr/bin/env python3
"""Fresh complete positive chains and precise dishonest-protocol rejections."""
from pathlib import Path
import shutil
import subprocess
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
PALCS = ROOT / "src/Pal.Tool/bin/Debug/net10.0/palcs"
FSTAR = ROOT / "tools/run-fstar.sh"
SOURCE = (HERE / "Protocol.cs").read_text()
BASE = ["TranslationErrors", "Struct_StoreModel", "Class_Store",
        "Class_Other", "Struct_Store_Enumerator"]
BASE += ["Func_Store_" + m for m in
         ("_ctor", "Count", "Invalidate", "CopyTo", "Enumerator__ctor_Store_T__int",
          "Enumerator_MoveNext", "Enumerator_Current", "Enumerator_Dispose",
          "Enumerator_Reset", "Enumerator_IEnumerator_Current",
          "GetEnumerator", "IEnumerable1_GetEnumerator")]
BASE += ["Func_Other_Count", "Func_Other__ctor",
         "Func_ProtocolClient_Test", "Func_ProtocolClient_TestMiss", "Func_ProtocolClient_Terminal"]
BASE += ["Func_ProtocolClient_SnapshotOnly", "Func_ProtocolClient_GuardFalse", "Func_ProtocolClient_Forward"]
BASE += ["Func_ProtocolClient_LoopCast"]
TAIL = ["Func_Store_Trace", "Func_Store_Partial", "Func_ProtocolClient_Generic",
        "Func_ProtocolClient_Successful", "Func_ProtocolClient_Failed",
        "Func_ProtocolClient_StaticBox", "Func_ProtocolClient_StaticStruct", "Func_ProtocolClient_ForwardClient",
        "Func_ProtocolClient_Stale", "Func_ProtocolClient_LoopClient"]


def guarded(source, value=0):
    return source.replace(
        "IEnumerator<T> IEnumerable<T>.GetEnumerator() => GetEnumerator();",
        f"IEnumerator<T> IEnumerable<T>.GetEnumerator() => Count == {value} ? "
        "new Enumerator(this, 1) : GetEnumerator();").replace(
        '[Ensures("Pal.Exists((Store<T>.Enumerator e) => Pal.Boxes(Result, e) && ReferenceEquals(e._owner, @this) && e._index == 0)")]',
        f'[Ensures("Pal.Implies(@this.Elements.Length != {value}, Pal.Exists((Store<T>.Enumerator e) => '
        'Pal.Boxes(Result, e) && ReferenceEquals(e._owner, @this) && e._index == 0))")]')


def check(label, source, failure=None, diagnostic=False, guard_line=False):
    work = HERE / "obj" / label
    if work.exists():
        shutil.rmtree(work)
    out, cache = work / "out", work / "_cache"
    out.mkdir(parents=True)
    cache.mkdir()
    path = work / "Protocol.cs"
    path.write_text(source)
    result = subprocess.run([PALCS, "-o", out, path], text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    if diagnostic:
        code = diagnostic if isinstance(diagnostic, str) else "PALCS0866"
        if not result.returncode or code not in result.stdout:
            raise SystemExit(result.stdout)
        print(f"{label}: rejected with {code}", flush=True)
        return
    if result.returncode:
        raise SystemExit(result.stdout)
    modules = BASE + (["Func_Store_Trace", "Func_ProtocolClient_Successful"] if guard_line else TAIL)
    for module in modules:
        result = subprocess.run(
            [FSTAR, "--force", "--z3refresh", "--z3rlimit", "10",
             "--cache_checked_modules", "--cache_dir", cache,
             "--include", out, "--include", cache,
             "--include", ROOT / "pulse", "--include", ROOT / "pulse/_cache",
             "--already_cached", "Prims,FStar,Pulse,Pulse.Main,Pulse.Nolib,Pulse.Class,Pulse.Lib,PulseCore",
             out / (module + ".fst")], text=True,
            stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        if module == failure:
            if not result.returncode or (cache / (module + ".fst.checked")).exists():
                raise SystemExit(f"{label}: dishonest protocol unexpectedly verified")
            if not any(s in result.stdout for s in (
                    "Failed to prove", "Cannot prove:", "Cannot match the following slprop")):
                raise SystemExit(result.stdout)
            if guard_line:
                lines = (out / (module + ".fst")).read_text().splitlines()
                trace_line = next(i for i, text in enumerate(lines, 1)
                                  if "= func_Store_Trace " in text)
                line = next(i for i, text in enumerate(lines, 1)
                            if "assert (pure" in text and i < trace_line)
                if f"{module}.fst({line}," not in result.stdout:
                    raise SystemExit(f"Not a factory-selection failure:\n{result.stdout}")
            print(f"{label}: dependencies verified; {module} rejected", flush=True)
            return
        if result.returncode:
            raise SystemExit(f"{label}/{module} unexpectedly failed:\n{result.stdout}")
    if failure:
        raise SystemExit(f"did not exercise {failure}")
    print(f"{label}: all {len(modules)} modules freshly verified", flush=True)


def negative_forwarding():
    check("forward-open-loan", SOURCE.replace(
        "candidate.Count == 0", "SnapshotOnly(input)"), diagnostic=True)
    check("forward-different-target", SOURCE.replace(
        "return Test(input);", "return TestMiss(input);"), diagnostic=True)
    check("forward-invent-source", SOURCE.replace(
        "return e.MoveNext();", "return Test(input);"), diagnostic=True)


if sys.argv[1:] == ["positive"]:
    check("fresh", SOURCE)
    check("guarded", guarded(SOURCE))
elif sys.argv[1:] == ["negative"]:
    negative_forwarding()
    check("swallowed-stale", SOURCE.replace(
        "if (_revision != _owner._revision) throw new InvalidOperationException();", ""),
        "Func_Store_Enumerator_MoveNext")
    # Weakening the authored contracts cannot override the generated universal
    # laws on the actual nominal implementations.
    wrong_current = SOURCE.replace(
        '[Ensures("Pal.Same(Result, @this._current)")]\n        public T Current => _current!;',
        '[Ensures("Pal.Same(Result, default(T))")]\n        public T Current => default!;').replace(
        '[Ensures("Pal.Boxes(Result, @this._current)")]',
        '[Ensures("Pal.Boxes(Result, default(T))")]')
    check("wrong-current", wrong_current, "Func_Store_Enumerator_Current")
    wrong_move = SOURCE.replace(
        '[Ensures("@this.Ready && Result == (Pal.Old(@this._index) == 0)")]',
        '[Ensures("@this.Ready && !Result")]').replace(
        "if (_index == 0) { _current = _owner._items[0]; _index = 1; return true; }",
        "_index = 1;")
    check("wrong-move", wrong_move, "Func_Store_Enumerator_MoveNext")
    restart = SOURCE.replace('[Ensures("@this._index == 1")]', '[Ensures("true")]').replace(
        "            return false;", "            _index = 0; return false;")
    check("restart-after-end", restart, "Func_Store_Enumerator_MoveNext")
    wrong_dispose = SOURCE.replace(
        "public void Dispose() { }", "public void Dispose() { _owner._revision = 9; }")
    check("mutating-dispose", wrong_dispose, diagnostic="PALCS0734")
    partial_dispose = SOURCE.replace("public void Dispose() { }",
        'public void Dispose() { _index = 1; }')
    check("partial-dispose", partial_dispose, "Func_Store_Enumerator_Dispose")
    # A restrictive user precondition must not hide the arbitrary-prefix law.
    check("restricted-dispose", partial_dispose.replace(
        '[Ensures("true")]\n        public void Dispose()',
        '[Requires("@this._index == 1")]\n        [Ensures("true")]\n        public void Dispose()'),
        "Func_Store_Enumerator_Dispose")
    check("body-restricted-dispose", SOURCE.replace("public void Dispose() { }",
        "public void Dispose() { Pal.Requires(_index == 1); _index = 1; }"),
        "Func_Store_Enumerator_Dispose")
    check("bad-ranking", SOURCE.replace("Pal.Decreases(1 - e.Index);", "Pal.Decreases(1);"),
          "Func_Store_Trace")
    check("current-after-end", SOURCE.replace("return more && !end && !again;",
        "int invalid = e.Current;\n        return more && !end && !again;"),
        "Func_ProtocolClient_Terminal")
    # The unboxed traversal is still correct; the actual interface chooses a
    # different (already-ended) iterator. Selection must fail at the adapter.
    wrong_branch = guarded(SOURCE, 1).replace(
        "bool partial = source.Partial(true);", "bool partial = true;").replace(
        "bool empty = source.Partial(false);", "bool empty = true;")
    check("wrong-branch", wrong_branch, "Func_ProtocolClient_Successful", guard_line=True)
    check("missing-dispose", SOURCE.replace("        e.Dispose();\n    }", "\n    }"), diagnostic=True)
    check("wrong-slot", SOURCE.replace(
        "yield return e.Current;", "yield return default!;"), diagnostic=True)
    check("box-alias", SOURCE.replace(
        "bool result = true;", "IEnumerator<T> alias = e;\n        bool result = true;"), diagnostic=True)
    check("spec-key-collision", SOURCE.replace(
        '[Ensures("true")]\n        public void Dispose()',
        '[Ensures("true"), Ensures("true"), Ensures("true"), Ensures("true"), Ensures("true"), Ensures("true")]\n'
        '        public void Dispose_protocol() { }\n'
        '        [Ensures("true")]\n        public void Dispose()'), diagnostic="PALCS0501")
elif sys.argv[1:] == ["negative-forwarding"]:
    negative_forwarding()
else:
    raise SystemExit("usage: checks.py positive|negative|negative-forwarding")
