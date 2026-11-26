#!/usr/bin/env python3
"""Reject changing a retained view's identity or lying about virtual dispatch."""
from pathlib import Path
import shutil
import subprocess

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
source = (HERE / "Owner.cs").read_text()
cases = (
    ("reassign-owner", source.replace("bool moved = iterator.MoveNext();",
        "view = source.Select(9); bool moved = iterator.MoveNext();"), "PALCS0715", None),
    ("copy-iterator", source.replace("bool moved = iterator.MoveNext();",
        "var copy = iterator; bool moved = copy.MoveNext();"), "PALCS0710", None),
    ("wrong-dispatch", source.replace('[Ensures("Result == 7")]', '[Ensures("Result == 33")]'), None, "Func_BorrowedOwnerClient_Run"),
    ("wrong-window-result", source.replace(
        '[Ensures("Result == @this.SpecValue")]\n    public int ReadWindow(',
        '[Ensures("Result == @this.SpecValue + 1")]\n    public int ReadWindow('),
        None, "Func_Owner_ReadWindow"),
    ("stale-mutation-result", source.replace(
        '[Ensures("Result == next && @this.SpecValue == next")]\n    public int ChangeAndRead',
        '[Ensures("Result == Pal.Old(@this.SpecValue)")]\n    public int ChangeAndRead'),
        None, "Func_Owner_ChangeAndRead"),
    # Emitter regression: without the concrete snapshot, the checked return
    # trade cannot infer the erased model at the following readonly call.
    ("missing-handoff", source, None, "Func_Owner_ReadWindow"),
    ("wrong-ghost-frame", source.replace("    public Iterator GetEnumerator()",
        '    [Ensures("Pal.Same(@this.touches, Pal.Old(@this.touches))", At = typeof(Owner<>.Window))]\n'
        "    public Iterator GetEnumerator()"), None, "Func_Window_at_Owner_GetEnumerator"),
    ("identity-model-conflation", source.replace(
        '[Ensures("!ReferenceEquals(left.Identity, right.Identity)")]',
        '[Ensures("ReferenceEquals(left.Identity, right.Identity)")]'),
        None, "Func_BorrowedOwnerClient_SameModelDistinct"),
    ("view-identity-is-not-source", source.replace(
        "[Spec] public override Owner<T> Identity => source;",
        "[Spec] public override Owner<T> Identity => this;"), "PALCS0001", None),
    ("identity-model-only-composition", source.replace(
        "[Spec] public virtual Owner<T> Identity => this;",
        "[Spec] public virtual Owner<T> Identity => this;\n"
        "[Spec] public bool SelfIdentity => ReferenceEquals(this.Identity, this);"),
        "PALCS0001", None),
    ("wrong-branch-result", source.replace(
        '[Ensures("Result == 7")]\n    public static int Branch',
        '[Ensures("Result == 33")]\n    public static int Branch'),
        None, "Func_BorrowedOwnerClient_Branch"),
    ("missing-branch-packing", source, None, "Func_BorrowedOwnerClient_MutatingBranch"),
    ("wrong-closed-owner-result", source.replace(
        '[Ensures("Result == @this.SpecValue")]\n    public int ClosedOwnerReads',
        '[Ensures("Result == @this.SpecValue + 1")]\n    public int ClosedOwnerReads'),
        None, "Func_Owner_ClosedOwnerReads"),
    ("missing-read-close", source, None, "Func_Owner_ClosedOwnerReads"),
    # A write makes the owner mutable: do not pin it to its entry model or
    # silently restore it merely because a later ghost call asks for ownership.
    ("dirty-owner-handoff", source.replace(
        "int result = value;\n        HandoffProof.Inspect",
        "int result = value;\n        value = 0;\n        HandoffProof.Inspect"),
        None, "Func_Owner_ClosedOwnerReads"),
    ("wrong-iterator-peer", source.replace(
        "Iterator theirs = other.GetEnumerator();", "Iterator theirs = GetEnumerator();"),
        None, "Func_Window_at_Owner_Compare"),
    ("compare-view-is-not-source", source.replace(
        "bool inherited = view.Compare(other);", "bool inherited = source.Compare(other);"),
        None, "Func_BorrowedOwnerClient_CompareSelected"),
    ("copy-held-in-view", source.replace(
        "Iterator mine = GetEnumerator();",
        "Iterator mine = GetEnumerator(); Iterator copy = mine;"), "PALCS0710", None),
    ("wrong-retained-owner-frame", source.replace(
        "    public bool Compare(Owner<T> other)",
        '    [Ensures("Pal.Same(@this.touches, Pal.Old(@this.touches))", At = typeof(Owner<>.Window))]\n'
        "    public bool Compare(Owner<T> other)"),
        None, "Func_Window_at_Owner_Compare"),
    ("missing-view-loop-frame", source, None, "Func_Window_at_Owner_Compare"),
    ("missing-readonly-reindex", source, None, "Func_Window_at_Owner_ShortCircuit"),
    ("wrong-short-circuit-result", source.replace(
        "Result == (skip || @this.SpecValue == 7)", "Result == (skip || @this.SpecValue == 8)"),
        None, "Func_Window_at_Owner_ShortCircuit"),
    ("mutating-getter-not-readonly", source.replace(
        "public override int Stable => selected;",
        "public override int Stable { get { Pal.UpdateGhost(ref touches, OwnerFrame.Next(touches)); return selected; } }").replace(
        "    public bool ShortCircuit(bool skip)",
        '    [Ensures("Pal.Same(@this.touches, Pal.Old(@this.touches))", At = typeof(Owner<>.Window))]\n'
        "    public bool ShortCircuit(bool skip)"),
        None, "Func_Window_at_Owner_ShortCircuit"),
    ("current-mutates-owner", source.replace(
        "public int Current => value;",
        "public int Current { get { int ignored = owner.Value; return value; } }"),
        None, "Func_Owner_Iterator_ReadCurrent_owner_Window"),
    ("mutating-owner-not-frozen", source.replace(
        "        public bool MoveNext()",
        '        [Ensures("@this.SpecOwnerFlag == Pal.Old(@this.SpecOwnerFlag)")]\n'
        "        public bool MoveNext()"),
        None, "Func_Owner_Iterator_MoveNext_owner_Window"),
)
for name, text, diagnostic, module in cases:
    work = HERE / "obj" / name
    if work.exists():
        shutil.rmtree(work)
    work.mkdir(parents=True)
    shutil.copyfile(HERE / "OwnerFrameState.fst", work / "OwnerFrameState.fst")
    path = work / "Owner.cs"
    path.write_text(text)
    result = subprocess.run([ROOT / "src/Pal.Tool/bin/Debug/net10.0/palcs", "-o", work / "out", path, HERE / "Handoff.cs"],
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    if diagnostic:
        if not result.returncode or diagnostic not in result.stdout:
            raise SystemExit(result.stdout or f"{name} was not rejected")
    else:
        result.check_returncode()
        if name == "missing-handoff":
            generated = work / "out" / (module + ".fst")
            old = generated.read_text()
            handoff = "  assert (Class_Owner.class_Owner__inv var_this #perm_this pre_this);\n"
            if old.count(handoff) != 1:
                raise SystemExit("expected one checked handoff in ReadWindow")
            generated.write_text(old.replace(handoff, ""))
        if name == "missing-branch-packing":
            generated = work / "out" / (module + ".fst")
            old = generated.read_text()
            if old.count("Pulse.Lib.CSharp.RefJoin.") != 6:
                raise SystemExit("expected two arms packing both mutated records, and their unpacks")
            generated.write_text("".join(line for line in old.splitlines(keepends=True)
                                         if "Pulse.Lib.CSharp.RefJoin." not in line))
        if name == "missing-read-close":
            generated = work / "out" / (module + ".fst")
            old = generated.read_text()
            close = "  fold Class_Owner.class_Owner__inv var_this #perm_this pre_this;\n"
            if old.count(close) != 1:
                raise SystemExit("expected one closed-owner field-read bracket")
            generated.write_text(old.replace(close, ""))
        if name == "missing-view-loop-frame":
            generated = work / "out" / (module + ".fst")
            lines = generated.read_text().splitlines(keepends=True)
            frames = [line for line in lines if line.strip().startswith("(vself_")
                      and ".fld_audit ==" in line]
            if len(frames) != 1:
                raise SystemExit("expected one checked inherited ghost loop frame")
            generated.write_text("".join(line for line in lines if line not in frames))
        if name == "missing-readonly-reindex":
            generated = work / "out" / (module + ".fst")
            lines = generated.read_text().splitlines(keepends=True)
            assertions = [line for line in lines
                          if line.strip().startswith("assert (R.pts_to var_self vkept_record_")]
            if len(assertions) != 1:
                raise SystemExit("expected one checked readonly-state reindex")
            generated.write_text("".join(line for line in lines if line not in assertions))
        target = module + ".fst.checked"
        excluded = [target]
        if name == "mutating-getter-not-readonly":
            excluded.append("Func_Window_Stable.fst.checked")
        if name == "current-mutates-owner":
            excluded.append("Func_Owner_Iterator_Current_owner_Window.fst.checked")
        shutil.copytree(HERE / "_cache", work / "deps",
                        ignore=shutil.ignore_patterns(*excluded))
        cache = work / "_cache"
        cache.mkdir()
        result = subprocess.run([
            ROOT / "tools/run-fstar.sh", "--force", "--z3refresh", "--z3rlimit", "10",
            "--cache_checked_modules", "--cache_dir", cache,
            "--include", work / "out", "--include", work / "deps", "--include", cache,
            "--include", ROOT / "pulse/_cache",
            "--already_cached", "Prims,FStar,Pulse,Pulse.Main,Pulse.Nolib,Pulse.Class,Pulse.Lib,PulseCore",
            work / "out" / (module + ".fst")],
            stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
        expected = "Cannot prove" if name in (
            "missing-handoff", "missing-read-close", "dirty-owner-handoff") else "Failed to prove"
        if not result.returncode or (cache / target).exists() or expected not in result.stdout:
            raise SystemExit(result.stdout or "incorrect dispatch result verified")
    print(f"{name}: rejected as expected")
