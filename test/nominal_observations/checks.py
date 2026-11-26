#!/usr/bin/env python3
"""Source-level negative checks for checked observation slots."""
from pathlib import Path
import shutil
import subprocess
import re

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
TEXT = (HERE / "Observations.cs").read_text()
CASES = (
    ("wrong-count", TEXT.replace("public virtual int Count => 1;", "public virtual int Count => 2;"),
     None, "Func_Packet_Count"),
    ("source-not-view", TEXT.replace("cache = 0; return cache;", "cache = 1; return cache;"),
     None, "Func_Empty_Count"),
    ("wrong-comparer", TEXT.replace("public override IComparer<T> Comparer => selected;",
                                   "public override IComparer<T> Comparer => source.Comparer;"),
     None, "Func_Empty_Comparer"),
    ("changed-observation", TEXT.replace("public virtual IComparer<T> Comparer => order;",
        "public virtual IComparer<T> Comparer { get { order = Comparer<T>.Default; return order; } }"),
     "PALCS0866", None),
    ("original-domain", TEXT.replace("[EnumerationObservation(nameof(Items), Length = true)]",
        '[Requires("false")]\n    [EnumerationObservation(nameof(Items), Length = true)]'),
     None, "Func_ObservationClient_Ordinary"),
    ("not-spec", TEXT.replace("EnumerationObservation(nameof(Order))", "EnumerationObservation(nameof(Comparer))"),
     "PALCS0866", None),
    ("wrong-length-type", TEXT.replace("EnumerationObservation(nameof(Order))",
                                      "EnumerationObservation(nameof(Order), Length = true)"),
     "PALCS0866", None),
    ("hidden-observation", TEXT.replace("public override IComparer<T> Order => selected;",
                                       "public new IComparer<T> Order => selected;"),
     "PALCS0866", None),
    ("no-unchecked-installation", TEXT + """
public static class UnknownDispatch
{
    [Ensures("true")]
    public static bool Test(Packet<int> source) => ObservationClient.Observe(source);
}
""", "PALCS0866", None),
    ("unknown-generic-subclass", TEXT + """
public static class UnknownGeneric
{
    [Ensures("true")]
    public static bool Test<T>(Packet<T> source) => ObservationClient.Observe(source);
}
""", "PALCS0866", None),
    ("interface-reimplementation", TEXT.replace("public sealed class Empty : Packet<T>",
        "public sealed class Empty : Packet<T>, IEnumerable<T>").replace(
        "private int cache;", """private int cache;
        IEnumerator<T> IEnumerable<T>.GetEnumerator() => throw new NotSupportedException();"""),
     "PALCS0866", None),
    ("reassigned-source", TEXT.replace("bool hit = Observe(packet);",
        "packet = new Packet<T>(item, comparer); bool hit = Observe(packet);"),
     "PALCS0866", None),
    ("parenthesized-reassignment", TEXT.replace("bool hit = Observe(packet);",
        "(packet) = new Packet<T>(item, comparer); bool hit = Observe(packet);"),
     "PALCS0866", None),
    ("forwarded-capability", TEXT.replace("int again = candidate.Count;",
        "bool forwarded = Observe(source); int again = candidate.Count;"),
     "PALCS0866", None),
    ("concrete-helper-escape", TEXT.replace("int again = candidate.Count;",
        "bool forwarded = Observe(candidate); int again = candidate.Count;"),
     "PALCS0866", None),
    ("iterator-slot", TEXT.replace("int again = candidate.Count;",
        "using IEnumerator<T> iterator = candidate.GetEnumerator(); int again = candidate.Count;"),
     "PALCS0866", None),
    ("missing-copy-evidence", TEXT.replace("public virtual void CopyTo", "public virtual void NotCopyTo")
         .replace("public override void CopyTo", "public override void NotCopyTo"),
     "PALCS0866", None),
    ("wrong-copy", TEXT.replace("array[index] = item;", "array[index] = default(T);"),
     None, "Func_Packet_CopyTo"),
    ("wrong-enumeration", TEXT.replace("yield return item;", "yield return default(T);"),
     None, "Func_Packet_GetEnumerator"),
)

for name, text, diagnostic, target in CASES:
    assert text != TEXT, name
    work = HERE / "obj" / name
    if work.exists():
        shutil.rmtree(work)
    work.mkdir(parents=True)
    (work / "Observations.cs").write_text(text)
    out = work / "out"
    run = subprocess.run([ROOT / "src/Pal.Tool/bin/Debug/net10.0/palcs", "-o", out, work / "Observations.cs"],
                         stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    if diagnostic:
        assert run.returncode and diagnostic in run.stdout, (name, run.stdout)
    else:
        assert run.returncode == 0, (name, run.stdout)
        cache = work / "_cache"
        cache.mkdir()
        # Recheck every changed dependency, not just the target client.
        for checked in (HERE / "_cache").glob("*.checked"):
            source = checked.name.removesuffix(".checked")
            original = HERE / "out" / source
            changed = out / source
            if changed.exists() and original.exists() and changed.read_bytes() == original.read_bytes():
                shutil.copyfile(checked, cache / checked.name)
        if name == "original-domain":
            # Its getter has an intentionally empty domain. Verify that getter,
            # then test that the client cannot establish the unchanged domain.
            positive = subprocess.run([ROOT / "tools/run-fstar.sh", "--include", ROOT / "pulse/_cache",
                "--include", out, "--include", cache, "--cache_checked_modules", "--cache_dir", cache,
                out / "Func_Packet_Count.fst"], stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
            assert positive.returncode == 0, positive.stdout
        run = subprocess.run([ROOT / "tools/run-fstar.sh", "--include", ROOT / "pulse/_cache",
            "--include", out, "--include", cache, out / f"{target}.fst"],
            stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
        assert run.returncode != 0 and ("Error" in run.stdout or "error" in run.stdout), (name, run.stdout)
    print("rejected:", name, flush=True)

# No collection/member-name whitelist: the identical C# algorithm and checked
# installation work after renaming both the nominal class and observation slots.
renamed = TEXT
for before, after in (("Packet", "Envelope"), ("Items", "Values"), ("Order", "Relation"),
                      ("Count", "Size"), ("Comparer", "Ordering")):
    renamed = re.sub(r"\b" + before + r"\b", after, renamed)
work = HERE / "obj" / "renamed"
work.mkdir(parents=True, exist_ok=True)
(work / "Observations.cs").write_text(renamed)
run = subprocess.run(["make", "-C", str(HERE), "cs", "verify",
    "SOURCES=obj/renamed/Observations.cs", "OUT=obj/renamed/out", "CACHE_DIR=obj/renamed/_cache"],
    stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
assert run.returncode == 0, run.stdout
print("verified: renamed nominal class and observation slots", flush=True)

consumer = (HERE / "out" / "Func_ObservationClient_Observe.fst").read_text()
assert "Enumerable.Capability.read" in consumer
assert "Class_Packet.class_Packet__inv" not in consumer
installers = list((HERE / "out").glob("Nominal_ObservationClient_View_*.fst"))
assert installers
for installer in installers:
    generated = installer.read_text()
    assert "Func_Empty_Count.func_Empty_Count" in generated
    assert "Func_Empty_Comparer.func_Empty_Comparer" in generated
    assert "exists*" in generated and "R.pts_to x.state" in generated
    assert "Func_Packet_Count.func_Packet_Count" not in generated
print("checked: generated view ownership and actual slots", flush=True)
view_client = (HERE / "out" / "Func_ObservationClient_View.fst").read_text()
assert len(re.findall(r"let (t\d+) = !var_view;.*?var_view := \1;", view_client, re.S)) == 2
print("checked: snapshot instrumentation restores both view records before lending", flush=True)
