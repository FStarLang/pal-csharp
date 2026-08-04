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

    // -----------------------------------------------------------------------
    // §10. Recursive classes. `C?` is `option class_C`, the invariant is stated at the
    // *option* so that null is a pattern the prover can case on (R10.3), and six lemmas
    // take it apart. Nothing here is per-example: every name is a function of the class.
    // -----------------------------------------------------------------------

    /// <summary>R10.2. The nullable object reference, <c>option class_C</c>.</summary>
    public static string ClassOpt(string name) => "class_" + name + "__opt";

    /// <summary>R10.3. The primitive, model-recursive invariant, stated at the option.</summary>
    public static string ClassInvOpt(string name) => "class_" + name + "__inv_opt";

    /// <summary>R10.4. <c>Some? x &lt;==&gt; </c> the model is a non-empty constructor.</summary>
    public static string ClassCases(string name) => "class_" + name + "__cases";

    /// <summary>R10.4. The null case, preserving the invariant.</summary>
    public static string ClassNilCase(string name) => "class_" + name + "__nil_case";

    /// <summary>R10.4. The null case, consuming the invariant.</summary>
    public static string ClassElimNil(string name) => "class_" + name + "__elim_nil";

    /// <summary>R10.4. Re-establishing the invariant of a null reference.</summary>
    public static string ClassIntroNil(string name) => "class_" + name + "__intro_nil";

    /// <summary>R10.4. Opening a non-null reference into its fields and sub-invariants.</summary>
    public static string ClassElimCons(string name) => "class_" + name + "__elim_cons";

    /// <summary>R10.4. Closing it again.</summary>
    public static string ClassIntroCons(string name) => "class_" + name + "__intro_cons";
    public static string ClassIntro(string name) => "class_" + name + "__intro";
    public static string ClassAsOpt(string name) => "class_" + name + "__as_opt";

    /// <summary>R10.8. The recursive share/gather of a recursive class, at the option.</summary>
    public static string ClassInvOptShare(string name) => ClassInvOpt(name) + "_share";
    public static string ClassInvOptGather(string name) => ClassInvOpt(name) + "_gather";

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

    /// <summary>
    /// R9.15a. The upcast as a value, <em>keeping</em> the index. It is one operation and
    /// not two because Pulse matches resources by name: a <c>let</c> that rebinds the
    /// reference after a separate ghost step would leave the invariant attached to the old
    /// term. The plain form is one <c>forget_impl</c> away and the index is not recoverable
    /// once dropped, so the conversion hands back the more informative resource and
    /// R9.16's downcast is what makes use of it.
    /// </summary>
    public static string UpcastToAt(string name, string baseName) =>
        "class_" + name + "__to_" + baseName + "_at";

    /// <summary>
    /// R9.18. The same conversion with the index dropped, for a reference whose object
    /// record this method never knew — a base-typed parameter, say. A leaf needs no such
    /// form because a leaf reference always *is* its record; a class in the middle of a
    /// hierarchy can be handed one from outside, and must still be convertible.
    /// </summary>
    public static string UpcastTo(string name, string baseName) =>
        "class_" + name + "__to_" + baseName;

    /// <summary>
    /// R9.18. The four primitives every class in a hierarchy publishes, and the reason a
    /// class at depth three needs no new dispatch rule.
    ///
    /// <para><c>is</c> is the proposition "this reference denotes this object record";
    /// <c>ref</c> makes the reference from the record; <c>obj_at</c> recovers the record
    /// from the reference. Stated that way they are the *whole* of what an encoding has to
    /// supply — everything else in §9, the two invariants, pack and unpack, dispatch,
    /// share and gather, the upcast and the downcast, is written once against them and is
    /// the same text at the root and at an intermediate class. What differs between the
    /// two is three definitions: at the root a reference is a dyn and <c>obj_at</c> is one
    /// recovery; at an intermediate class a reference is its parent's and <c>obj_at</c>
    /// follows the parent's <c>sub</c> field, which is one recovery more.</para>
    /// </summary>
    public static string ClassIs(string name) => "class_" + name + "__is";
    public static string ClassRef(string name) => "class_" + name + "__ref";
    public static string ClassObjAt(string name) => "class_" + name + "__obj_at";

    /// <summary>
    /// R9.18. Opening and closing the indexed invariant. They are what a *descendant*
    /// needs — it has to get at the resource its parent's invariant is carrying in order to
    /// re-read it at its own model — and they are the only way to, since the definition is
    /// not exported.
    /// </summary>
    public static string ClassIntroAt(string name) => "class_" + name + "__intro_at";
    public static string ClassElimAt(string name) => "class_" + name + "__elim_at";

    /// <summary>
    /// R9.18. An intermediate class's <em>view</em>: the parent object record a value of
    /// this class presents itself as. The parent's <c>sub</c> field carries this class's
    /// record back, so both directions are pure functions and every cast is free.
    /// </summary>
    public static string ClassView(string name) => "class_" + name + "__view";

    /// <summary>R9.18. The parent vtable derived from any vtable of this class.</summary>
    public static string ClassBasePkg(string name, string baseName) =>
        ClassAsBase(name, baseName) + "_pkg";

    /// <summary>
    /// R9.18. The derived implementation of an inherited method: this class's vtable
    /// dispatching one level down, re-read at the parent's model. It is what lets a
    /// subclass of an intermediate class implement that class's vtable only and get its
    /// grandparent's for free.
    /// </summary>
    public static string ClassPkgSlot(string name, string method) =>
        "class_" + name + "__pkg_" + method;

    /// <summary>
    /// R9.17. The two primitives that make the dyn an implementation detail: <c>pack</c>
    /// turns an object record into a reference, <c>unpack</c> turns a reference whose
    /// index is known back into the representation it was built from. Every subclass goes
    /// through them, so <c>FStar.Dyn</c> appears in exactly one emitted module.
    /// </summary>
    public static string ClassPack(string name) => "class_" + name + "__pack";
    public static string ClassUnpack(string name) => "class_" + name + "__unpack";

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
        // R10.2. A nullable reference is `option class_C`, named through the class's own
        // abbreviation so that every rule below reads the same whether or not the class
        // is recursive.
        IrClassType { Nullable: true } c => $"{Names.ClassModule(c.Name)}.{Names.ClassOpt(c.Name)}",
        IrClassType c => $"{Names.ClassModule(c.Name)}.{Names.ClassType(c.Name)}",
        IrSpecListType l => $"list {Render(l.Element)}",
        IrSpecTreeType t => $"CTree.tree {Render(t.Element)}",
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
