using Pal.Compiler.Ir;

namespace Pal.Compiler.Emit;

/// <summary>
/// What a Pulse term denotes, so that the emitter can insert the one coercion the
/// C#-to-Pulse gap requires — <c>Int32.v</c> between a machine integer and the
/// mathematical integer a specification talks about — and no others.
/// </summary>
public enum TermKind
{
    /// <summary>A mathematical <c>int</c> / <c>nat</c>.</summary>
    Math,
    /// <summary>A machine integer such as <c>Int32.t</c>.</summary>
    Machine,
    Bool,
    Prop,
    /// <summary>A <c>Seq.seq</c>.</summary>
    Seq,
    /// <summary>A live Pulse <c>array</c>.</summary>
    Array,
    Other,
}

/// <summary>A Pulse term together with what it denotes.</summary>
public readonly record struct Term(string Text, TermKind Kind, IrType? Type = null)
{
    public override string ToString() => Text;
}

/// <summary>Naming conventions (doc/translation.md R2.1).</summary>
public static class Names
{
    public static string Local(string name) => "var_" + name;
    public static string Argument(string name) => "arg_" + name;
    public static string Function(string name) => "func_" + name;
    public static string SpecFunction(string name) => "spec_" + name;
    public static string Lemma(string name) => "lemma_" + name;
    public static string FunctionModule(string name) => "Func_" + name;
    public static string SpecModule(string name) => "Let_" + name;

    // R3.4. A struct's field names are prefixed and always used module-qualified, so a
    // C# field can never collide with a Pulse keyword, with the preamble, or with
    // another struct's field of the same name.
    public static string StructModule(string name) => "Struct_" + name;
    public static string StructType(string name) => "struct_" + name;
    public static string StructRaw(string name) => "struct_" + name + "__raw";
    public static string StructPred(string name) => "struct_" + name + "__pred";
    public static string Field(string name) => "fld_" + name;

    /// <summary>The module-qualified projection <c>e.Struct_S.fld_f</c> (F10).</summary>
    public static string Projection(string structName, string field) =>
        StructModule(structName) + "." + Field(field);

    // §3.4. A class emits five constructs, all in one module: the representation record,
    // the object-reference type, the refined model type (predicate plus abbreviation),
    // and the model-indexed invariant. Field names are shared with R3.4 verbatim, so
    // field access and field update need no class-specific rule.
    public static string ClassModule(string name) => "Class_" + name;
    public static string ClassType(string name) => "class_" + name;
    public static string ClassRaw(string name) => "class_" + name + "__raw";
    public static string ClassInv(string name) => "class_" + name + "__inv";

    // R3.10d. The three ghost lemmas that make an object shareable. They are per class,
    // not once in the support library, because their proofs recurse into the class's own
    // fields — each array's `share`, each sub-object's `share` (F22).
    /// <summary>
    /// R4.11b's permission binder for a parameter the emitter — not the author — decided
    /// is observed rather than owned. It is prefixed rather than taken from the source so
    /// that it cannot collide with a `[Frac("p")]` name the author chose.
    /// </summary>
    public static string Permission(string parameter) => "perm_" + parameter;

    public static string ClassInvShare(string name) => ClassInv(name) + "_share";
    public static string ClassInvGather(string name) => ClassInv(name) + "_gather";
    public static string ClassInvGatherGen(string name) => ClassInv(name) + "_gather_gen";

    /// <summary>
    /// R3.10d. The second copy of an existential inside <c>gather</c>, which holds two
    /// views of one object at once. The prefix cannot collide with a real binder: every
    /// name <see cref="Contents"/> and <see cref="SubModel"/> produce begins with
    /// <c>contents_</c> or <c>model_</c>, so nothing they generate starts with <c>alt_</c>.
    /// </summary>
    public static string Alt(string binder) => "alt_" + binder;

    // R3.9d. The refined model type is named after the *class*, not after the model type:
    // an atomic model such as `SpecInt` has no user-declared struct to refine, and two
    // classes sharing a model type must not collide.
    public static string ClassModel(string name) => "class_" + name + "__model";
    public static string ClassModelPred(string name) => "class_" + name + "__model__pred";

    // -----------------------------------------------------------------------
    // §9. Inheritance. An abstract class emits a vtable, an object record, the dyn it
    // is reached through, and the two invariants (indexed and plain); a leaf emits the
    // M2 constructs unchanged plus a forgetting function, a base-model view of its own
    // invariant, a vtable value and an upcast.
    // -----------------------------------------------------------------------

    /// <summary>R9.9. The vtable type of an abstract class.</summary>
    public static string ClassVtbl(string name) => "class_" + name + "__vtbl";

    /// <summary>R9.9. A vtable slot for a virtual method.</summary>
    public static string VtblSlot(string method) => "vfn_" + method;

    /// <summary>R9.9. The fully applied object: a vtable together with a representation.</summary>
    public static string ClassObj(string name) => "class_" + name + "__obj";

    /// <summary>R9.9. Ownership of a <em>known</em> object record, named apart so a fold has a witness (F34).</summary>
    public static string ClassAt(string name) => "class_" + name + "__at";

    /// <summary>R9.10. The invariant with the object record named — the primitive form.</summary>
    public static string ClassInvAt(string name) => "class_" + name + "__inv_at";

    /// <summary>R9.10. Throwing the index away, which is one ghost step and irreversible.</summary>
    public static string ClassForgetImpl(string name) => "class_" + name + "__forget_impl";

    /// <summary>R9.12. The dispatching wrapper for a virtual method, at the index and plain.</summary>
    public static string Dispatch(string className, string method) =>
        "class_" + className + "_" + method;
    public static string DispatchAt(string className, string method) =>
        Dispatch(className, method) + "_at";

    /// <summary>R9.6. The base's model as a function of this class's model.</summary>
    public static string ClassForget(string name) => "class_" + name + "__forget";

    /// <summary>R9.14. This class's invariant seen at its base's model.</summary>
    public static string ClassAsBase(string name, string baseName) =>
        "class_" + name + "__as_" + baseName;

    /// <summary>R9.14. The vtable <em>value</em>, and the object record built from it.</summary>
    public static string VtblModule(string name) => "Vtbl_" + name;
    public static string ClassVtblValue(string name) => "class_" + name + "__vtbl_value";
    public static string ClassObjOf(string name) => "class_" + name + "__obj_of";

    /// <summary>R9.15. The upcast, at the index and plain.</summary>
    public static string UpcastAt(string name) => "class_" + name + "__upcast_at";
    public static string Upcast(string name) => "class_" + name + "__upcast";

    /// <summary>
    /// R9.15. The upcast as a value: the same ghost step, followed by the reference the
    /// base-typed name is bound to. It exists because Pulse matches resources by name — a
    /// `let` that rebinds a reference after the ghost step leaves the invariant attached
    /// to the wrong term — so the C# conversion becomes one call rather than two steps.
    /// </summary>
    public static string UpcastTo(string name, string baseName) =>
        "class_" + name + "__to_" + baseName;

    /// <summary>
    /// R9.15a. The upcast as a value, <em>keeping</em> the index. This is the one the
    /// emitter uses: the plain form is one <c>forget_impl</c> away and the index is not
    /// recoverable once dropped, so the conversion hands back the more informative
    /// resource and R9.16's downcast is what makes use of it.
    /// </summary>
    public static string UpcastToAt(string name, string baseName) =>
        UpcastTo(name, baseName) + "_at";

    /// <summary>R9.16. The leaf representation, re-erased so the next <c>recover</c> has its equation.</summary>
    public static string ClassBox(string name) => "class_" + name + "__box";

    /// <summary>R9.16. The chain walker: recovers the object record and hands back its representation.</summary>
    public static string ClassRep(string name) => "class_" + name + "__rep";

    /// <summary>R9.16. The checked downcast from <paramref name="baseName"/> to this class.</summary>
    public static string DowncastFrom(string name, string baseName) =>
        "class_" + name + "__from_" + baseName;

    /// <summary>
    /// A member's own name, undoing the type qualifier <c>Naming.Of</c> prefixes. The
    /// qualifier is what keeps two classes' <c>Area</c> methods in distinct modules; the
    /// bare name is what a vtable slot and a dispatching wrapper are named after.
    /// </summary>
    public static string Member(string qualified, string className) =>
        qualified.StartsWith(className + "_", StringComparison.Ordinal)
            ? qualified[(className.Length + 1)..]
            : qualified;

    /// <summary>A <c>[Spec]</c> member of a class: a pure function of the model (R3.9c).</summary>
    public static string Observation(string className, string member) =>
        "spec_" + className + "_" + member;

    /// <summary>
    /// R3.10a. The invariant's existential for the contents of an array field. The field
    /// itself is the reference; this is what it points to, and it is what every
    /// specification mentioning the field actually denotes.
    /// </summary>
    public static string Contents(string field) => "contents_" + field;

    /// <summary>
    /// R3.10b. The invariant's existential for the model of an object field. Exactly
    /// parallel to <see cref="Contents"/>: the field itself is the reference, and this is
    /// what every specification mentioning the field denotes — a sub-object is summarised
    /// by its model as an array is summarised by its contents.
    /// </summary>
    public static string SubModel(string field) => "model_" + field;

    /// <summary>The class-qualified field projection <c>e.Class_C.fld_f</c> (F10).</summary>
    public static string ClassProjection(string className, string field) =>
        ClassModule(className) + "." + Field(field);

    /// <summary>The receiver of an instance method (R4.10a). Spelled <c>@this</c> in C#.</summary>
    public const string This = "this";

    /// <summary>The ghost model binder threaded through an instance method (R4.10).</summary>
    public const string Model = "var_model";

    /// <summary>The post-state model an instance method's <c>ensures</c> quantifies (R4.10).</summary>
    public const string ModelPost = "var_model_post";

    public const string Result = "var_result";
}

/// <summary>The Pulse rendering of a C# type (doc/translation.md §3).</summary>
public static class Types
{
    public static string Machine(PrimKind kind) => kind switch
    {
        PrimKind.Bool => "bool",
        PrimKind.SByte => "I8.t",
        PrimKind.Byte => "U8.t",
        PrimKind.Short => "I16.t",
        PrimKind.UShort => "U16.t",
        PrimKind.Int => "I32.t",
        PrimKind.UInt => "U32.t",
        PrimKind.Long => "I64.t",
        PrimKind.ULong => "U64.t",
        PrimKind.Char => "U16.t",
        PrimKind.Void => "unit",
        PrimKind.SpecInt => "int",
        PrimKind.SpecNat => "nat",
        PrimKind.SlProp => "slprop",
        _ => "unit",
    };

    /// <summary>The F* module qualifying a machine integer's operations.</summary>
    public static string Module(PrimKind kind) => kind switch
    {
        PrimKind.SByte => "I8",
        PrimKind.Byte => "U8",
        PrimKind.Short => "I16",
        PrimKind.UShort => "U16",
        PrimKind.Int => "I32",
        PrimKind.UInt => "U32",
        PrimKind.Long => "I64",
        PrimKind.ULong => "U64",
        PrimKind.Char => "U16",
        _ => "I32",
    };

    /// <summary>Bit width, used by the R5.9 case-2 measure.</summary>
    public static int Width(PrimKind kind) => kind switch
    {
        PrimKind.SByte or PrimKind.Byte => 8,
        PrimKind.Short or PrimKind.UShort or PrimKind.Char => 16,
        PrimKind.Long or PrimKind.ULong => 64,
        _ => 32,
    };

    public static bool IsSigned(PrimKind kind) =>
        kind is PrimKind.SByte or PrimKind.Short or PrimKind.Int or PrimKind.Long;

    public static string Render(IrType type) => type switch
    {
        IrPrim p => Machine(p.Kind),
        IrArrayType a => $"array {Render(a.Element)}",
        IrSeqType s => $"Seq.seq {Render(s.Element)}",
        IrGhostType g => Render(g.Inner),
        IrNamedType n => $"{Names.StructModule(n.Name)}.{Names.StructType(n.Name)}",
        IrClassType c => $"{Names.ClassModule(c.Name)}.{Names.ClassType(c.Name)}",
        IrPulseType p => p.PulseText,
        _ => "unit",
    };

    /// <summary>The literal syntax for a value of a machine-integer type.</summary>
    public static string Literal(object? value, IrType? type)
    {
        switch (value)
        {
            case null: return "()";
            case bool b: return b ? "true" : "false";
        }

        var kind = (type as IrPrim)?.Kind ?? PrimKind.Int;
        var text = Convert.ToString(value, System.Globalization.CultureInfo.InvariantCulture) ?? "0";
        var suffix = kind switch
        {
            PrimKind.Int => "l",
            PrimKind.Long => "L",
            PrimKind.UInt => "ul",
            PrimKind.ULong => "uL",
            PrimKind.Short => "s",
            PrimKind.UShort => "us",
            PrimKind.SByte => "y",
            PrimKind.Byte => "uy",
            PrimKind.SpecInt or PrimKind.SpecNat => "",
            _ => "l",
        };
        return text.StartsWith('-') ? $"({text}{suffix})" : text + suffix;
    }
}
