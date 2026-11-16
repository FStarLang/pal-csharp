"""Ghost storage is a logical field, not a CLR getter or a fresh permission."""
import subprocess
import sys
import tempfile
from pathlib import Path

here = Path(__file__).resolve().parent
root = here.parent.parent
tool = sys.argv[1]


def translate(source, directory):
    return subprocess.run(
        [tool, "--reference", str(here / "out"), "-o", str(directory), str(source)],
        text=True, capture_output=True,
    )


header = "using System; using PalLang; using PalCSharp.Tests;\n"
stub = 'public ref OwnerState State => throw new InvalidOperationException("Specification only");'
property_decl = '[GhostField("OwnerSpec.Make(0)")] ' + stub


def owner(member=property_decl, body="", extra=""):
    return header + "public class Probe { [Model] private int Model => 0; " + member + (
        " public void Bad() {" + body + "} " if body else ""
    ) + extra + " }"


negatives = {
    "discarded-getter": (owner(body="_ = State;"), "PALCS0771"),
    "runtime-read": (owner(body="OwnerState s = State;"), "PALCS0771"),
    "qualified-read": (owner(body="_ = this.State;"), "PALCS0771"),
    "ref-escape": (owner(body="ref OwnerState s = ref State;"), "PALCS0771"),
    "direct-write": (owner(body="State = OwnerSpec.Make(1);"), "PALCS0771"),
    "ordinary-ref-call": (owner(body="Use(ref State);",
        extra="static void Use(ref OwnerState s) {}"), "PALCS0771"),
    "ref-return": (owner(extra="public ref OwnerState Escape() => ref State;"), "PALCS0771"),
    "value-property": (owner(member=property_decl.replace("ref OwnerState", "OwnerState")), "PALCS0770"),
    "readonly-ref": (owner(member=property_decl.replace("ref OwnerState", "ref readonly OwnerState")), "PALCS0770"),
    "static-property": (owner(member=property_decl.replace("public ref", "public static ref")), "PALCS0770"),
    "virtual-property": (owner(member=property_decl.replace("public ref", "public virtual ref")), "PALCS0770"),
    "indexer": (owner(member=property_decl.replace("State =>", "this[int index] =>")), "PALCS0770"),
    "backing-storage": (owner(member='[GhostField("OwnerSpec.Make(0)")] public OwnerState State { get; set; }'), "PALCS0770"),
    "backing-ref": (owner(member=property_decl.replace(
        'throw new InvalidOperationException("Specification only")', "ref backing"),
        extra="private OwnerState backing;"), "PALCS0770"),
    "effectful-accessor": (owner(member=property_decl.replace(
        '=> throw new InvalidOperationException("Specification only");',
        '{ get { Console.WriteLine("effect"); throw new InvalidOperationException(); } }')), "PALCS0770"),
    "spec-observation": (owner(member="[Spec] " + property_decl), "PALCS0770"),
    "wrong-initializer-type": (owner(member=property_decl.replace("OwnerSpec.Make(0)", "1")), "PALCS0100"),
    "dependent-initializer": (owner(member=property_decl.replace("OwnerSpec.Make(0)", "State")), "PALCS0100"),
    "effectful-initializer": (owner(member=property_decl.replace("OwnerSpec.Make(0)", "Probe.Effect()"),
        extra="public static OwnerState Effect() => OwnerSpec.Make(0);"), "PALCS0772"),
    "interface": (header + "public interface IProbe { [GhostField(\"OwnerSpec.Make(0)\")] ref OwnerState State { get; } }", "PALCS0770"),
    "interface-implementation": (header + "public interface IProbe { ref OwnerState State { get; } } "
        + "public class Probe : IProbe { [Model] private int Model => 0; " + property_decl + " }", "PALCS0770"),
    "struct": (header + "public struct Probe { " + property_decl + " }", "PALCS0770"),
    "unrepresented-subclass": (header + """
[assembly: TranslateAnnotatedOnly]
public class Base<T> {
    [Model] private SpecInt Model => 0;
}
public sealed class Probe<T> : Base<T> {
    [GhostField("OwnerSpec.Make(0)")]
    private ref OwnerState State => throw new InvalidOperationException();
}
""", "PALCS0770"),
}

with tempfile.TemporaryDirectory(prefix="pal-ghost-storage-") as temporary:
    directory = Path(temporary)
    for name, (text, code) in negatives.items():
        source = directory / (name + ".cs")
        source.write_text(text)
        result = translate(source, directory / name)
        output = result.stdout + result.stderr
        assert result.returncode != 0, "Accepted invalid ghost storage: " + name
        assert code in output, name + ": " + output

    # No constructor, no update and no read: the declaration itself must reject
    # informative F* storage, in both modeled and plain classes.
    for classification in ("modeled", "plain"):
        source = directory / (classification + ".cs")
        source.write_text(header + """
[SpecType("Prims.int")] public readonly struct Informative {}
public static class BadSpec {
    [SpecOp("Prims.int_zero")] public static Informative Zero() => throw new InvalidOperationException();
}
""" + ("[Plain] " if classification == "plain" else "") + """
public sealed class InformativeStorage {
    [GhostField("BadSpec.Zero()")]
    private ref Informative State => throw new InvalidOperationException();
""" + ("[Model] private int Model => 0;" if classification == "modeled" else "") + "}")
        out = directory / classification
        result = translate(source, out)
        assert result.returncode == 0, result.stdout + result.stderr
        checked = subprocess.run(
            [str(root / "tools/run-fstar.sh"), "--include", str(out),
             "--include", str(root / "pulse/_cache"), "--already_cached", "*",
             str(out / "Class_InformativeStorage.fst")], text=True, capture_output=True,
        )
        output = checked.stdout + checked.stderr
        assert checked.returncode != 0 and "erased" in output, output
        assert "Identifier not found" not in output, output

raw = (here / "out/Class_GhostStorageOwner.fst").read_text()
assert "fld_state: GhostStorageState.state ty_T;" in raw
assert "require_erased (id #(GhostStorageState.state ty_T))" in raw
for method in ("AdvanceProof", "ViaAlias"):
    text = (here / ("out/Func_GhostStorageOwner_" + method + ".fst")).read_text()
    assert "B.op_Colon_Equals var_this" in text
    assert "exists*" in text.split("ensures", 1)[1], "Ghost-only update was marked read-only"
primary = (here / "out/Func_GhostStorageOwner__ctor_int.fst").read_text()
chained = (here / "out/Func_GhostStorageOwner__ctor_unit.fst").read_text()
assert primary.count("GhostStorageState.make ty_T 0l") == 1
assert "GhostStorageState.make" not in chained
assert "get_State" not in raw and "get_state" not in raw

print(f"Ghost storage: {len(negatives)} frontend negatives, two declaration-time erased-type negatives, "
      "generic/alias updates and exactly-once constructor initialization checked")
