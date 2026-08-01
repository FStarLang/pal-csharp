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

public enum CalleeKind { Method, Spec, Lemma }

/// <summary>A call to a user method, <c>[Spec]</c> function, or <c>[Lemma]</c>.</summary>
public sealed record IrCall(IrLoc Loc, string Callee, ImmutableArray<IrExpr> Args) : IrExpr(Loc)
{
    /// <summary>Resolved by Collect; tells Emit which module the callee lives in.</summary>
    public CalleeKind Kind { get; init; } = CalleeKind.Method;
}

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

/// <summary><c>Pal.Contents(a)</c> — the ghost <c>Seq</c> view of an array.</summary>
public sealed record IrContents(IrLoc Loc, IrExpr Array) : IrExpr(Loc);

public enum SeqOpKind { Length, Index, SetAt, Slice, IsPermutation }

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

public enum GhostKind { Assert, Assume, Raw, LemmaCall }

/// <summary><c>Pal.Assert</c> / <c>Pal.Assume</c> / <c>Pal.GhostStmt</c> / a <c>[Lemma]</c> call.</summary>
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

public sealed record IrFieldDecl(IrLoc Loc, string Name, IrType Type, string? Refinement);

/// <summary>A struct: emitted as <c>Struct_&lt;Name&gt;.fst</c>.</summary>
public sealed record IrStruct(
    IrLoc Loc,
    string Name,
    ImmutableArray<IrFieldDecl> Fields,
    ImmutableArray<string> Refinements) : IrDecl(Loc, Name);

/// <summary>Raw Pulse pulled in via <c>[assembly: IncludePulse]</c>.</summary>
public sealed record IrIncludePulse(IrLoc Loc, string Module, string Text) : IrDecl(Loc, Module);

/// <summary>The whole translation unit.</summary>
public sealed record IrProgram(ImmutableArray<IrDecl> Declarations);
