using System.Collections.Immutable;

namespace Pal.Compiler.Ir;

/// <summary>
/// Where an IR node came from in the C# source. Every node carries one so that
/// diagnostics point at real spans and so the provenance lint can check that no
/// emitted construct was invented by the translator.
/// </summary>
public sealed record IrLoc(string File, int Line, int Column, int EndLine, int EndColumn)
{
    public static readonly IrLoc None = new("<none>", 0, 0, 0, 0);

    public override string ToString() => $"{File}({Line},{Column})";
}

// ---------------------------------------------------------------------------
// Types (doc/translation.md §3)
// ---------------------------------------------------------------------------

public enum PrimKind
{
    Void,
    Bool,
    SByte, Byte,
    Short, UShort,
    Int, UInt,
    Long, ULong,
    Char,
    /// <summary>Spec-only mathematical integer (<c>SpecInt</c>).</summary>
    SpecInt,
    /// <summary>Spec-only mathematical natural (<c>SpecNat</c>).</summary>
    SpecNat,
    /// <summary>Spec-only separation-logic proposition.</summary>
    SlProp,
}

public abstract record IrType
{
    public sealed override string ToString() => Describe();
    protected abstract string Describe();
}

public sealed record IrPrim(PrimKind Kind) : IrType
{
    protected override string Describe() => Kind.ToString();

    public static readonly IrPrim Void = new(PrimKind.Void);
    public static readonly IrPrim Bool = new(PrimKind.Bool);
    public static readonly IrPrim Int = new(PrimKind.Int);
    public static readonly IrPrim SpecIntType = new(PrimKind.SpecInt);

    /// <summary>True for the machine-integer primitives (those with overflow obligations).</summary>
    public bool IsMachineInt => Kind is PrimKind.SByte or PrimKind.Byte or PrimKind.Short
        or PrimKind.UShort or PrimKind.Int or PrimKind.UInt or PrimKind.Long or PrimKind.ULong
        or PrimKind.Char;

    public bool IsSpecNumeric => Kind is PrimKind.SpecInt or PrimKind.SpecNat;
}

/// <summary>A C# array, <c>T[]</c>. Owned as a Pulse <c>array</c> plus its contents.</summary>
public sealed record IrArrayType(IrType Element) : IrType
{
    protected override string Describe() => $"{Element}[]";
}

/// <summary>The spec-only ghost sequence <c>Seq&lt;T&gt;</c>.</summary>
public sealed record IrSeqType(IrType Element) : IrType
{
    protected override string Describe() => $"Seq<{Element}>";
}

/// <summary>The spec-only ghost box <c>Ghost&lt;T&gt;</c>.</summary>
public sealed record IrGhostType(IrType Inner) : IrType
{
    protected override string Describe() => $"Ghost<{Inner}>";
}

/// <summary>A named user type (struct) translated to <c>Struct_&lt;name&gt;</c>.</summary>
/// <summary>
/// A reference to a translated <c>class</c> (R3.8): a <c>Box.box</c> of the class's
/// representation, carrying an invariant and a model rather than a value.
/// </summary>
public sealed record IrClassType(string Name, bool Nullable = false) : IrType
{
    protected override string Describe() => Nullable ? Name + "?" : Name;

    /// <summary>R10.2. The same class, held through an <c>option</c>.</summary>
    public IrClassType AsNullable => Nullable ? this : this with { Nullable = true };

    /// <summary>The non-null form, which R10.3a derives the nullable one from.</summary>
    public IrClassType AsNonNull => Nullable ? this with { Nullable = false } : this;
}

/// <summary>The spec-only inductive list <c>SpecList&lt;T&gt;</c> (R10.5), F*'s <c>list</c>.</summary>
public sealed record IrSpecListType(IrType Element) : IrType
{
    protected override string Describe() => $"SpecList<{Element}>";
}

/// <summary>
/// The spec-only inductive tree <c>SpecTree&lt;T&gt;</c> (R10.5),
/// <c>Pulse.Lib.CSharp.Tree.tree</c>.
/// </summary>
public sealed record IrSpecTreeType(IrType Element) : IrType
{
    protected override string Describe() => $"SpecTree<{Element}>";
}

public sealed record IrNamedType(string Name) : IrType
{
    protected override string Describe() => Name;
}

/// <summary>A type declared only in Pulse, via <c>[PulseType]</c>.</summary>
public sealed record IrPulseType(string Name, string PulseText) : IrType
{
    protected override string Describe() => Name;
}

// ---------------------------------------------------------------------------
// Expressions (doc/translation.md §6)
// ---------------------------------------------------------------------------

public enum UnOp { Neg, Not, BitNot }

public enum BinOp
{
    Add, Sub, Mul, Div, Rem,
    And, Or,                     // short-circuiting (R6.3)
    BitAnd, BitOr, BitXor, Shl, Shr,
    Eq, Ne, Lt, Le, Gt, Ge,
    Implies, Iff,                // spec-only
}

public abstract record IrExpr(IrLoc Loc)
{
    /// <summary>Filled in by the Elab pass; null before then.</summary>
    public IrType? Type { get; init; }
}

public sealed record IrLiteral(IrLoc Loc, object? Value) : IrExpr(Loc);

/// <summary>
/// The <c>null</c> literal (R10.2). A distinct node rather than an <see cref="IrLiteral"/>
/// with a null value, because that is also what a lowering error produces, and the two must
/// not be confused.
/// </summary>
public sealed record IrNull(IrLoc Loc) : IrExpr(Loc);

/// <summary>
/// An operation on the ghost inductive list <c>SpecList&lt;T&gt;</c> (R10.5).
/// <see cref="ListOpKind.Empty"/> and <see cref="ListOpKind.Cons"/> are its constructors,
/// and it is those two that R10.5 reads a recursive class's invariant off.
/// </summary>
public enum ListOpKind { Empty, Cons, Append, Length, Head, Tail, Index, IsEmpty }

public sealed record IrListOp(IrLoc Loc, ListOpKind Op, ImmutableArray<IrExpr> Args) : IrExpr(Loc);

/// <summary>An operation on the ghost inductive tree <c>SpecTree&lt;T&gt;</c> (R10.5).</summary>
public enum TreeOpKind { Leaf, Branch, Size, Elements, IsLeaf, Insert }

public sealed record IrTreeOp(IrLoc Loc, TreeOpKind Op, ImmutableArray<IrExpr> Args) : IrExpr(Loc);

/// <summary>A read of a local, parameter, or ghost binder.</summary>
public sealed record IrVar(IrLoc Loc, string Name) : IrExpr(Loc);

public sealed record IrUnary(IrLoc Loc, UnOp Op, IrExpr Operand) : IrExpr(Loc);

public sealed record IrBinary(IrLoc Loc, BinOp Op, IrExpr Left, IrExpr Right) : IrExpr(Loc);

public sealed record IrConditional(IrLoc Loc, IrExpr Cond, IrExpr Then, IrExpr Else) : IrExpr(Loc);

/// <summary><c>a[i]</c> on a real array (a memory read).</summary>
public sealed record IrElement(IrLoc Loc, IrExpr Array, IrExpr Index) : IrExpr(Loc);

/// <summary><c>a.Length</c> on a real array.</summary>
public sealed record IrLength(IrLoc Loc, IrExpr Array) : IrExpr(Loc);

/// <summary><c>x.f</c> on a struct.</summary>
public sealed record IrField(IrLoc Loc, IrExpr Receiver, string Field) : IrExpr(Loc);

/// <summary>
/// R3.9c. A <c>[Spec]</c> member of a class read off an object: <c>@this.Count</c>.
/// It is a pure function of the object's <em>model</em>, never of its representation,
/// which is what lets a caller — who holds only the model — use it at all.
/// </summary>
public sealed record IrObserve(
    IrLoc Loc, string Class, string Member, IrExpr Receiver) : IrExpr(Loc);

public sealed record IrFieldInit(string Field, IrExpr Value)
{
    /// <summary>
    /// The field's <em>declared</em> type. R3.5 lets a field be a spec-only type
    /// (R3.9a), so an <c>int</c> initialiser may have to cross into the mathematical
    /// world; §6's rule is that the conversion goes where the target type says so, and
    /// only the declaration knows that.
    /// </summary>
    public IrType? FieldType { get; init; }
}

/// <summary>
/// <c>new S { … }</c>, <c>new S()</c> or <c>default(S)</c> (R3.5). Every field of the
/// struct is present: C# guarantees a value type is fully initialized at construction,
/// so a field the source did not mention carries its type's zero.
/// </summary>
public sealed record IrNew(
    IrLoc Loc, string Struct, ImmutableArray<IrFieldInit> Fields) : IrExpr(Loc);

public enum CalleeKind { Method, Spec, Lemma }

/// <summary>A call to a user method, <c>[Spec]</c> function, or <c>[Lemma]</c>.</summary>
public sealed record IrCall(IrLoc Loc, string Callee, ImmutableArray<IrExpr> Args) : IrExpr(Loc)
{
    /// <summary>
    /// R4.11. The callee is an instance method that may move its receiver's model, so the
    /// caller must existentially quantify the receiver's post-state model rather than
    /// carry the one it was given.
    /// </summary>
    public bool MutatesReceiver { get; init; }

    /// <summary>
    /// Whether <c>Args[0]</c> is a receiver rather than an ordinary argument. R5.12 needs
    /// the distinction that <see cref="MutatesReceiver"/> alone cannot draw: a *read-only*
    /// instance call and a static call both leave it false, and only the first is known to
    /// leave its first argument's model where it was.
    /// </summary>
    public bool HasReceiver { get; init; }

    /// <summary>Resolved by Collect; tells Emit which module the callee lives in.</summary>
    public CalleeKind Kind { get; init; } = CalleeKind.Method;

    /// <summary>
    /// The callee's declared result type, when the frontend could map it. Emit needs it
    /// to know whether a <see cref="CalleeKind.Spec"/> application denotes a proposition
    /// or a mathematical value (R4.6).
    /// </summary>
    public IrType? ResultType { get; init; }
}

/// <summary>
/// An argument passed by reference: the <c>ref</c>/<c>out</c>/<c>in</c> at a call site
/// (R6.10). It is not an expression a C# programmer can write anywhere else, and it
/// never appears in a specification; it exists so that Emit can pass the callee the
/// <em>cell</em> rather than the cell's current contents.
/// </summary>
public sealed record IrRefArg(IrLoc Loc, IrExpr Operand) : IrExpr(Loc);

/// <summary>An explicit numeric conversion, <c>(long)e</c>.</summary>
public sealed record IrConvert(IrLoc Loc, IrType Target, IrExpr Operand) : IrExpr(Loc);

// --- spec-only expression forms -------------------------------------------

/// <summary><c>Pal.Old(e)</c> — the value of <c>e</c> in the pre-state.</summary>
public sealed record IrOld(IrLoc Loc, IrExpr Operand) : IrExpr(Loc);

/// <summary><c>Pal.Result&lt;T&gt;()</c> / bare <c>return</c> in an <c>[Ensures]</c>.</summary>
public sealed record IrResult(IrLoc Loc) : IrExpr(Loc);

/// <summary><c>Pal.Live(x)</c> — an explicit ownership assertion.</summary>
public sealed record IrLive(IrLoc Loc, IrExpr Operand) : IrExpr(Loc);

public sealed record IrBinder(string Name, IrType Type);

public sealed record IrQuantifier(
    IrLoc Loc, bool IsForall, ImmutableArray<IrBinder> Binders, IrExpr Body) : IrExpr(Loc);

/// <summary>
/// <c>new T[n]</c> (R6.9). Executable only: an array is a resource, so it has no meaning
/// in a specification.
/// </summary>
public sealed record IrNewArray(IrLoc Loc, IrType Element, IrExpr Length) : IrExpr(Loc);

/// <summary><c>Pal.Contents(a)</c> — the ghost <c>Seq</c> view of an array.</summary>
public sealed record IrContents(IrLoc Loc, IrExpr Array) : IrExpr(Loc);

public enum SeqOpKind { Length, Index, SetAt, Slice, Rotate, IsPermutation }

/// <summary>An operation on ghost sequences.</summary>
public sealed record IrSeqOp(IrLoc Loc, SeqOpKind Op, ImmutableArray<IrExpr> Args) : IrExpr(Loc);

/// <summary>
/// The measure R5.9 case 2 supplies for a counted loop: the distance from
/// <paramref name="Counter"/> to the bound of its own machine-integer type. It is a
/// distinct node because it is emitter-generated and must be visible to the provenance
/// lint as such.
/// </summary>
public sealed record IrTypeBoundMeasure(IrLoc Loc, string Counter, bool Increasing) : IrExpr(Loc);

/// <summary>Raw Pulse text spliced in verbatim (<c>Pal.InlinePulse</c>).</summary>
public sealed record IrInlinePulse(IrLoc Loc, string Text) : IrExpr(Loc);

// ---------------------------------------------------------------------------
// Statements (doc/translation.md §5)
// ---------------------------------------------------------------------------

public abstract record IrStmt(IrLoc Loc);

public sealed record IrBlock(IrLoc Loc, ImmutableArray<IrStmt> Statements) : IrStmt(Loc);

public sealed record IrLocalDecl(IrLoc Loc, string Name, IrType Type, IrExpr? Init) : IrStmt(Loc);

public sealed record IrAssign(IrLoc Loc, IrExpr Target, IrExpr Value) : IrStmt(Loc);

public sealed record IrIf(IrLoc Loc, IrExpr Cond, IrStmt Then, IrStmt? Else) : IrStmt(Loc);

public sealed record CountedFor(string Counter, bool Increasing);

public sealed record IrWhile(
    IrLoc Loc,
    IrExpr Cond,
    ImmutableArray<IrExpr> Invariants,
    IrExpr? Decreases,
    IrStmt Body) : IrStmt(Loc)
{
    /// <summary>
    /// Set by Normalize when this loop came from a counted <c>for</c>: the counter's
    /// name and whether it increases. Consumed by R5.9 case 2.
    /// </summary>
    public CountedFor? Counted { get; init; }

    /// <summary>Locals the body never assigns; R5.8b fixes their value in the invariant.</summary>
    public ImmutableArray<string> Unassigned { get; init; } = ImmutableArray<string>.Empty;

    /// <summary>Locals the loop needs ownership of; inferred by Elab (R5.8).</summary>
    public ImmutableArray<string> Live { get; init; } = ImmutableArray<string>.Empty;

    /// <summary>
    /// The step of the <c>for</c> this loop was desugared from (R5.7). It is kept apart
    /// from the body rather than appended to it because C# runs the step after a
    /// <c>continue</c> but not after a <c>break</c>, which is a distinction the body's
    /// escape guard cannot make (R5.10).
    /// </summary>
    public ImmutableArray<IrStmt> Step { get; init; } = ImmutableArray<IrStmt>.Empty;
}

/// <summary>
/// A <c>for</c> loop, kept intact by lowering and desugared to <see cref="IrWhile"/> by
/// the Normalize pass (R5.7).
/// </summary>
public sealed record IrFor(
    IrLoc Loc,
    ImmutableArray<IrStmt> Init,
    IrExpr? Cond,
    ImmutableArray<IrStmt> Step,
    ImmutableArray<IrExpr> Invariants,
    IrExpr? Decreases,
    IrStmt Body) : IrStmt(Loc);

public sealed record IrReturn(IrLoc Loc, IrExpr? Value) : IrStmt(Loc);

public sealed record IrExprStmt(IrLoc Loc, IrExpr Expr) : IrStmt(Loc);

public sealed record IrBreak(IrLoc Loc) : IrStmt(Loc);

public sealed record IrContinue(IrLoc Loc) : IrStmt(Loc);

public enum GhostKind { Assert, Assume, Raw, LemmaCall, Share, Gather }

/// <summary><c>Pal.Assert</c> / <c>Pal.Assume</c> / <c>Pal.GhostStmt</c> / <c>Pal.Share</c> /
/// <c>Pal.Gather</c> / a <c>[Lemma]</c> call.</summary>
public sealed record IrGhostStmt(IrLoc Loc, GhostKind Kind, IrExpr? Prop, string? Text) : IrStmt(Loc);

// ---------------------------------------------------------------------------
// Declarations (doc/translation.md §2, §4)
// ---------------------------------------------------------------------------

public enum ParamMode { Value, Ref, Out, In }

public sealed record IrParam(
    IrLoc Loc,
    string Name,
    IrType Type,
    ParamMode Mode)
{
    public bool IsGhost { get; init; }
    /// <summary>Ownership is transferred to the callee (<c>[Consumes]</c>).</summary>
    public bool Consumes { get; init; }
    /// <summary>Passed by value with no resource (<c>[Plain]</c>).</summary>
    public bool Plain { get; init; }
    /// <summary>Fractional-permission variable name (<c>[Frac("p")]</c>), if any.</summary>
    public string? Fraction { get; init; }
}

public abstract record IrDecl(IrLoc Loc, string Name);

/// <summary>An executable method: emitted as <c>Func_&lt;Name&gt;.fst</c>.</summary>
public sealed record IrMethod(
    IrLoc Loc,
    string Name,
    ImmutableArray<IrParam> Parameters,
    IrType ReturnType,
    ImmutableArray<IrExpr> Requires,
    ImmutableArray<IrExpr> Ensures,
    IrExpr? Decreases,
    IrStmt? Body) : IrDecl(Loc, Name)
{
    public bool IsLemma { get; init; }
    public string? PulseBody { get; init; }
    public bool Admit { get; init; }
    /// <summary>Expressions this method preserves (<c>[Preserves]</c>).</summary>
    public ImmutableArray<IrExpr> Preserves { get; init; } = ImmutableArray<IrExpr>.Empty;

    /// <summary>
    /// The class this is an instance member of, if any (§4.5). A non-null value is what
    /// makes the emitter thread a model binder and bracket the body with
    /// <c>unfold</c>/<c>fold</c>.
    /// </summary>
    public string? DeclaringClass { get; init; }

    /// <summary>A constructor: it allocates and establishes the invariant (R4.12).</summary>
    public bool IsConstructor { get; init; }

    /// <summary>
    /// R9.9. An <c>abstract</c> method of an abstract class: a vtable slot rather than a
    /// module. It is an ordinary <see cref="IrMethod"/> with no <see cref="Body"/>, so its
    /// contract is bound and lowered by exactly the machinery every other method uses —
    /// which is the point, since R9.7 makes this the only place that contract is written.
    /// </summary>
    public bool IsAbstract { get; init; }

    /// <summary>
    /// R4.11: the method assigns no field, so its contract collapses to
    /// <c>preserves class_C__inv this m</c> and its closing <c>fold</c> names the
    /// pre-state model binder rather than a recomputed model (R4.11a).
    /// </summary>
    public bool IsReadOnly { get; init; }

    /// <summary>
    /// R9.7. An <c>override</c> of a base class's <c>abstract</c> method. Its receiver is
    /// owned through <c>class_C__as_B</c> at <em>B</em>'s model, not through its own
    /// invariant, because the vtable slot it fills is typed at the base's model.
    /// </summary>
    public string? Overrides { get; init; }
}

/// <summary>A <c>[Spec]</c> pure function: emitted as <c>Let_&lt;Name&gt;.fst</c> (R4.6).</summary>
public sealed record IrSpecFunction(
    IrLoc Loc,
    string Name,
    ImmutableArray<IrParam> Parameters,
    IrType ReturnType,
    ImmutableArray<IrExpr> Requires,
    IrExpr Body) : IrDecl(Loc, Name)
{
    public bool IsRecursive { get; init; }
    public IrExpr? Decreases { get; init; }
}

public sealed record IrFieldDecl(IrLoc Loc, string Name, IrType Type)
{
    /// <summary>R10.10. A back pointer: constrained by the invariant, not owned by it.</summary>
    public bool IsBackward { get; init; }
}

/// <summary>One argument of a recursive class's model constructor (R10.5).</summary>
public abstract record IrRecArg;

/// <summary>An argument that is a pure expression over the non-recursive fields.</summary>
public sealed record IrRecPure(IrExpr Value) : IrRecArg;

/// <summary>An argument that is a recursive field's own model, <c>f.M</c>.</summary>
public sealed record IrRecField(string Field) : IrRecArg;

/// <summary>Which inductive spec type a recursive class is modelled by (R10.5).</summary>
public enum RecursiveShape { List, Tree }

/// <summary>
/// R10.5. The induction the emitter reads off a recursive class's <c>[Model]</c> member:
/// the constructor's arguments, in order, each either pure or a recursive field. This is
/// the whole of what §10 extracts from the user's notation — the predicate, the six case
/// lemmas and the recursive share/gather are all functions of it.
/// </summary>
public sealed record IrRecursion(
    RecursiveShape Shape,
    ImmutableArray<IrRecArg> Args,
    string? BackwardField)
{
    /// <summary>The recursive fields, in constructor-argument order.</summary>
    public ImmutableArray<string> RecursiveFields =>
        [.. Args.OfType<IrRecField>().Select(a => a.Field)];
}

/// <summary>A struct: emitted as <c>Struct_&lt;Name&gt;.fst</c> (R3.4).</summary>
public sealed record IrStruct(
    IrLoc Loc,
    string Name,
    ImmutableArray<IrFieldDecl> Fields,
    ImmutableArray<IrExpr> Refinements) : IrDecl(Loc, Name)
{
    /// <summary>
    /// R3.9a. <c>[Spec]</c> on a struct makes it a *spec-only* type: erased, never
    /// present in executable code, and — unlike an ordinary struct — free to hold
    /// spec-only field types such as <c>Seq&lt;T&gt;</c> and <c>SpecInt</c>.
    /// </summary>
    public bool IsSpecOnly { get; init; }
}

/// <summary>A <c>[Spec]</c> member of a class: a pure function of the model (R3.9c).</summary>
public sealed record IrObservation(
    IrLoc Loc,
    string Name,
    IrType ReturnType,
    IrExpr Body);

/// <summary>
/// A <c>sealed class</c>: emitted as <c>Class_&lt;Name&gt;.fst</c> (§3.4).
/// </summary>
/// <param name="Fields">The representation (R3.7).</param>
/// <param name="ModelType">
/// The <c>[Model]</c> member's return type — the model is <em>declared</em> by the user
/// and never derived by the emitter (R3.9).
/// </param>
/// <param name="ModelBody">
/// The abstraction relation (R3.9b): an expression over the fields, whose value is the
/// model. Inlined as a conjunct of the invariant rather than factored into a function,
/// because it is partial and factoring it would force a refinement to be discharged at
/// every use of the model.
/// </param>
/// <param name="ModelRefinements">
/// <c>[Refine]</c> clauses on the <c>[Model]</c> member: facts about the model alone,
/// which must live in the model's *type* or no caller can see them (R3.9d, F17).
/// </param>
/// <param name="Invariants">
/// <c>[Invariant]</c> clauses: facts about the fields, which are temporarily false inside
/// a method and so live inside the predicate, in the <c>unfold</c>/<c>fold</c> window.
/// </param>
public sealed record IrClass(
    IrLoc Loc,
    string Name,
    ImmutableArray<IrFieldDecl> Fields,
    string ModelMember,
    IrType ModelType,
    IrExpr? ModelBody,
    ImmutableArray<IrExpr> ModelRefinements,
    ImmutableArray<IrExpr> Invariants,
    ImmutableArray<IrObservation> Observations) : IrDecl(Loc, Name)
{
    /// <summary>
    /// R9.1. The translated class this one derives from, if any. Non-null and
    /// <see cref="IsAbstract"/> false is a leaf; null and abstract is a root.
    /// </summary>
    public string? BaseClass { get; init; }

    /// <summary>
    /// R9.1/R9.2. An <c>abstract class</c>: no representation, no
    /// <see cref="ModelBody"/>, and a vtable rather than a record.
    /// </summary>
    public bool IsAbstract { get; init; }

    /// <summary>
    /// R9.6. The <c>override</c> of the base's <c>[Model]</c> member: the base's model
    /// as an expression over <em>this</em> class's model. It is the forgetting function,
    /// and it is what makes a subclass a refinement of its parent rather than merely a
    /// class that happens to have the same methods.
    /// </summary>
    public IrExpr? ForgetBody { get; init; }

    /// <summary>True when this class participates in the M3 encoding rather than M2's.</summary>
    public bool InHierarchy => IsAbstract || BaseClass is not null;

    /// <summary>
    /// R10.5. Non-null when the class has a field of its own nullable type, in which case
    /// the invariant is an induction (R10.3) rather than a flat <c>exists*</c>, and
    /// <see cref="ModelBody"/> is not used: the induction replaces it.
    /// </summary>
    public IrRecursion? Recursion { get; init; }
}

/// <summary>Raw Pulse pulled in via <c>[assembly: IncludePulse]</c>.</summary>
public sealed record IrIncludePulse(IrLoc Loc, string Module, string Text) : IrDecl(Loc, Module);

/// <summary>The whole translation unit.</summary>
public sealed record IrProgram(ImmutableArray<IrDecl> Declarations);
