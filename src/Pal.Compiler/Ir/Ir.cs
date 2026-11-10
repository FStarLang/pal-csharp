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
    /// <summary>R20.3. <c>decimal</c>, as <c>Pulse.Lib.CSharp.Decimal.decimal</c>.</summary>
    Decimal,
    /// <summary>R20.3. <c>string</c>, as an F* <c>string</c>: an immutable value.</summary>
    String,
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

    /// <summary>
    /// True for the machine integers that can hold a negative value. This is the
    /// question <c>/</c> and <c>%</c> turn on: C# rounds them toward zero and F* toward
    /// minus infinity, and the two answers differ only when an operand is negative.
    /// </summary>
    public bool IsSignedMachineInt => Kind is PrimKind.SByte or PrimKind.Short
        or PrimKind.Int or PrimKind.Long;
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

/// <summary>
/// R17.1. <c>Span&lt;T&gt;</c> and <c>ReadOnlySpan&lt;T&gt;</c>, owned as a
/// <c>Pulse.Lib.Slice.slice</c> plus its contents.
/// </summary>
/// <remarks>
/// A span is a borrowed window on memory somebody else owns, and it is a distinct slot
/// kind rather than an array because of what it can do that an array cannot: be taken out
/// of a parent and given back. The two are otherwise indistinguishable — same contents
/// model (a <c>Seq</c>), same length, same subscript, same <c>[Frac]</c> — which is why
/// nearly every rule that mentions one mentions both.
///
/// Read-only-ness is not recorded here. <c>ReadOnlySpan&lt;T&gt;</c> differs only in
/// carrying an implicit fraction (R17.2), which the frontend reads off the Roslyn symbol,
/// and in rejecting writes, which C# itself does (R17.4).
/// </remarks>
public sealed record IrSpanType(IrType Element) : IrType
{
    protected override string Describe() => $"Span<{Element}>";
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
    protected override string Describe()
    {
        var head = TypeArguments.IsEmpty
            ? Name
            : $"{Name}<{string.Join(", ", TypeArguments)}>";
        return Nullable ? head + "?" : head;
    }

    /// <summary>
    /// R15.3. The class's type arguments, in declaration order, as Roslyn resolved them.
    /// Empty for a non-generic class, which is every class before M9.
    /// </summary>
    public ImmutableArray<IrType> TypeArguments { get; init; } = [];

    /// <summary>R10.2. The same class, held through an <c>option</c>.</summary>
    public IrClassType AsNullable => Nullable ? this : this with { Nullable = true };

    /// <summary>The non-null form, which R10.3a derives the nullable one from.</summary>
    public IrClassType AsNonNull => Nullable ? this with { Nullable = false } : this;

    /// <summary>
    /// R12.1. The class is <c>[Plain]</c>: it has a representation and nothing else, so
    /// every rule that would attach an invariant, a model or a case lemma to a value of
    /// this type has nothing to attach.
    /// </summary>
    public bool Plain { get; init; }
}

/// <summary>The spec-only inductive list <c>SpecList&lt;T&gt;</c> (R10.5), F*'s <c>list</c>.</summary>
public sealed record IrSpecListType(IrType Element) : IrType
{
    protected override string Describe() => $"SpecList<{Element}>";
}

/// <summary>
/// R11.1. A specification-only type the <em>user</em> declared, with <c>[SpecType]</c>.
/// <see cref="FStar"/> is the F* type it denotes and <see cref="Args"/> its type
/// arguments, in declaration order.
///
/// <para>This is the node that replaces a family of primitives. The translator knows
/// nothing about such a type beyond the two strings the user wrote, which is the point:
/// there is no C# specification type it can express that another cannot.</para>
/// </summary>
public sealed record IrUserSpecType(string Name, string FStar, ImmutableArray<IrType> Args) : IrType
{
    protected override string Describe() =>
        Args.IsEmpty ? Name : $"{Name}<{string.Join(", ", Args)}>";
}

public sealed record IrNamedType(string Name) : IrType
{
    protected override string Describe() =>
        TypeArguments.IsEmpty ? Name : $"{Name}<{string.Join(", ", TypeArguments)}>";

    /// <summary>R22.6. A generic <c>[Spec]</c> struct's type arguments, in declaration order.</summary>
    public ImmutableArray<IrType> TypeArguments { get; init; } = [];
}

/// <summary>
/// R14.4. A method's type parameter, in type position. The name is the C# one (<c>T</c>);
/// R14.3 is what turns it into a Pulse binder name, since F* reserves an initial capital
/// for constructors and modules.
/// </summary>
public sealed record IrTypeParamType(string Name) : IrType
{
    protected override string Describe() => Name;
}

/// <summary>
/// R19.1. An exception: F*'s open type <c>exn</c>. <see cref="Name"/> is the exception
/// class declared in the program, rendered as the refinement of <c>exn</c> to that class
/// and its subclasses; null is <c>System.Exception</c>, which is all of <c>exn</c>.
/// </summary>
public sealed record IrExnType(string? Name) : IrType
{
    protected override string Describe() => Name ?? "Exception";
}

/// <summary>R20.3. <c>Nullable&lt;T&gt;</c> of a value type: F*'s <c>option</c>.</summary>
public sealed record IrOptionType(IrType Inner) : IrType
{
    protected override string Describe() => $"{Inner}?";
}

/// <summary>
/// R20.3. A delegate type, held opaquely: <c>Pulse.Lib.CSharp.Opaque.delegate "name"</c>.
/// R26.1. One of the BCL's callable delegates (<c>Predicate&lt;T&gt;</c>, <c>Action&lt;T&gt;</c>,
/// <c>Converter&lt;TIn, TOut&gt;</c>, <c>Comparison&lt;T&gt;</c>) carries its signature, and is
/// <c>Pulse.Lib.CSharp.Delegate.fn1 a r</c> or <c>fn2 a b r</c>.
/// </summary>
public sealed record IrDelegateType(string Name) : IrType
{
    public ImmutableArray<IrType> Params { get; init; } = [];
    public IrType? Return { get; init; }
    public bool Callable => Return is not null;
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
public enum ListOpKind
{
    Empty, Cons, Append, Length, Head, Tail, Index, IsEmpty,
    // R15.7. The vocabulary `FStar.List.Tot` does not already supply.
    Take, Drop, InsertAt, RemoveAt, Reverse,
}

public sealed record IrListOp(IrLoc Loc, ListOpKind Op, ImmutableArray<IrExpr> Args) : IrExpr(Loc);

/// <summary>
/// R11.2. An application of a user-declared specification operation: the F* term
/// <see cref="Function"/> applied to <see cref="Args"/>, left to right, with the receiver
/// first when there is one. A property, an instance method, a static method and a
/// discriminator all lower to this, because all four are applications.
/// </summary>
public sealed record IrSpecOp(IrLoc Loc, string Function, ImmutableArray<IrExpr> Args) : IrExpr(Loc)
{
    /// <summary>
    /// The declared type of each argument's parameter, positionally, or empty when the
    /// operation is not a method (a property has no parameters to declare). R10.2b/R10.2c
    /// read this: a class reference and a nullable one are different Pulse types, so an
    /// argument may need injecting or projecting, and only the declaration says which.
    /// </summary>
    public ImmutableArray<IrType?> ParamTypes { get; init; } = [];

    /// <summary>R27.17. The operation is a constant of a <c>[SpecType]</c> enum (R21.8).</summary>
    public bool EnumCase { get; init; }

    /// <summary>R27.22. The operation is a <c>[RegionOp]</c>, over a region's heap.</summary>
    public bool Region { get; init; }

    /// <summary>
    /// R33.4. The operation is a bound static member of a machine-integer type
    /// (<c>IntPtr.Size</c>): its value is a machine integer, which a contract reads through
    /// <c>.v</c>.
    /// </summary>
    public bool MachineValue { get; init; }

    /// <summary>
    /// R20.10. The operation models a BCL member over program values, so its arguments
    /// are at their machine types in a contract too -- `set.Contains(i)` asks about the
    /// `I32.t` <c>i</c>, not about <c>I32.v i</c>.
    /// </summary>
    public bool MachineArgs { get; init; }

    /// <summary>
    /// R11.3. When this is a <c>[SpecCtor]</c>, the F* name of its type's <em>empty</em>
    /// constructor — the sibling marked <c>Empty = true</c>. Null when this is an ordinary
    /// operation. It is carried here because §10 needs both constructors of a model, and a
    /// use of one is where the other becomes findable.
    /// </summary>
    public string? SiblingEmpty { get; init; }

    /// <summary>
    /// R14.5 for operations. The resolved type arguments of a generic <c>[SpecOp]</c>
    /// method, applied explicitly ahead of its value arguments.
    /// </summary>
    public ImmutableArray<IrType> TypeArgs { get; init; } = [];

    /// <summary>
    /// R26.3. The operation builds a sequence, so `==` with it is `Seq.equal` (R22.23).
    /// </summary>
    public bool Built { get; init; }
}

/// <summary>A read of a local, parameter, or ghost binder.</summary>
public sealed record IrVar(IrLoc Loc, string Name) : IrExpr(Loc);

public sealed record IrUnary(IrLoc Loc, UnOp Op, IrExpr Operand) : IrExpr(Loc);

public sealed record IrBinary(IrLoc Loc, BinOp Op, IrExpr Left, IrExpr Right) : IrExpr(Loc)
{
    /// <summary>R22.14. The operation wraps rather than carrying a no-overflow obligation.</summary>
    public bool Wraps { get; init; }
}

public sealed record IrConditional(IrLoc Loc, IrExpr Cond, IrExpr Then, IrExpr Else) : IrExpr(Loc);

/// <summary><c>a[i]</c> on a real array (a memory read).</summary>
public sealed record IrElement(IrLoc Loc, IrExpr Array, IrExpr Index) : IrExpr(Loc);

/// <summary><c>a.Length</c> on a real array.</summary>
public sealed record IrLength(IrLoc Loc, IrExpr Array) : IrExpr(Loc);

/// <summary>Where a borrowed span came from, and so which receipt it carries (R17.5).</summary>
public enum SpanOrigin
{
    /// <summary><c>Span&lt;T&gt; s = a;</c> and <c>a.AsSpan()</c> — the whole array.</summary>
    Array,
    /// <summary><c>a.AsSpan(i)</c> and <c>a.AsSpan(i, n)</c> — a window of an array.</summary>
    ArrayRange,
    /// <summary><c>s.Slice(i)</c>, <c>s.Slice(i, n)</c>, <c>s[i..j]</c> — a window of a span.</summary>
    SpanRange,
}

/// <summary>
/// R17.5. Borrowing a span out of an array or another span.
/// <see cref="Start"/> and <see cref="Length"/> are null exactly when
/// <see cref="Origin"/> is <see cref="SpanOrigin.Array"/>.
/// </summary>
public sealed record IrSpanCreate(
    IrLoc Loc,
    SpanOrigin Origin,
    IrExpr Source,
    IrExpr? Start,
    IrExpr? Length) : IrExpr(Loc);

/// <summary><c>x.f</c> on a struct.</summary>
public sealed record IrField(IrLoc Loc, IrExpr Receiver, string Field) : IrExpr(Loc)
{
    /// <summary>R27.44. A field of another object of the method's own class.</summary>
    public bool Peer { get; init; }
}

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

/// <summary>
/// R12.4. <c>new C { … }</c> on a <c>[Plain]</c> class: a box holding the record. There is
/// no constructor to call, because §12 emitted no constructor — a plain class is its
/// representation, so allocating one is building the record and boxing it.
/// </summary>
/// <summary>R19.1. <c>new E(args)</c> for an exception class <c>E</c>: a pure value.</summary>
public sealed record IrNewException(IrLoc Loc, string Class, ImmutableArray<IrExpr> Args) : IrExpr(Loc);

public sealed record IrAlloc(IrLoc Loc, string Class, IrNew Record) : IrExpr(Loc);

public enum CalleeKind
{
    Method, Spec, Lemma,
    /// <summary>
    /// R27.39. A call of a <c>[Callback]</c> parameter: <c>Callee</c> is the parameter, the
    /// first argument the variable naming its trace and the second the node.
    /// </summary>
    Callback,
}

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

    /// <summary>
    /// R27.45. The callee is a method (not a constructor) none of whose parameters is
    /// <c>[Consumes]</c>: every object argument's invariant comes back from the call.
    /// </summary>
    public bool KeepsArguments { get; init; }

    /// <summary>Resolved by Collect; tells Emit which module the callee lives in.</summary>
    public CalleeKind Kind { get; init; } = CalleeKind.Method;

    /// <summary>
    /// R14.5. The callee's type arguments, in declaration order, applied ahead of the
    /// value arguments. They come from Roslyn's resolved symbol, so an inferred call and
    /// an explicit <c>M&lt;int&gt;(…)</c> are translated identically.
    /// </summary>
    public ImmutableArray<IrType> TypeArguments { get; init; } = ImmutableArray<IrType>.Empty;

    /// <summary>
    /// R22.11. The callee is <c>[DoesNotReturn]</c>: a call to it is a throw point, so the
    /// caller hands back what it holds before the call, as it does before a <c>throw</c>.
    /// </summary>
    public bool DoesNotReturn { get; init; }

    /// <summary>
    /// R4.13. The callee's declared parameter types, in <see cref="Args"/> order (a
    /// receiver, when present, occupies the first slot with no declared type). An
    /// argument crossing into the mathematical world is C#'s implicit conversion from a
    /// machine integer to <c>SpecInt</c>, and it is the *parameter* that decides whether
    /// that crossing happens: a spec function or lemma may just as well take an `int`,
    /// and then the machine value must be passed as it stands.
    /// </summary>
    public ImmutableArray<IrType?> ParamTypes { get; init; } = [];

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

/// <summary>
/// R27.39. A lambda passed to a <c>[Callback]</c> parameter, lifted to the method
/// <c>Method</c>: its captured variables, in the order of the lifted method's parameters
/// (after the trace), each an <see cref="IrRefArg"/> when the lambda writes it.
/// </summary>
public sealed record IrLambdaRef(IrLoc Loc, string Method, ImmutableArray<IrExpr> Captures) : IrExpr(Loc)
{
    public ImmutableArray<IrType> TypeArguments { get; init; } = [];
    public IrCallback Callback { get; init; } = null!;

    /// <summary>R32.11. Whether the lambda's protocol states a bound on its calls.</summary>
    public bool Bounded { get; init; }
}

/// <summary>
/// R27.39. What a <c>[Callback]</c> delegate is called with and returns: a pointer into
/// <c>Region</c>, recorded in the trace by its <c>[Model]</c> view <c>View</c>.
/// </summary>
public sealed record IrCallback(IrClassType Region, IrType View, IrType Result)
{
    /// <summary>R32.11. <c>[Callback(Bounded = true)]</c>: the caller passes a bound on the calls.</summary>
    public bool Bounded { get; init; }
}

/// <summary>
/// R27.39. A lifted lambda: its first parameter is the trace, its last the node, and the
/// first clause of its contract each way is the protocol.
/// </summary>
public sealed record IrLambdaInfo(string Trace, string Node, IrCallback Callback)
{
    /// <summary>R32.11. The bound on the calls the protocol states, over the read-only captures.</summary>
    public IrExpr? Bound { get; init; }
}

/// <summary>An explicit numeric conversion, <c>(long)e</c>.</summary>
public sealed record IrConvert(IrLoc Loc, IrType Target, IrExpr Operand) : IrExpr(Loc);

/// <summary>
/// An expression whose evaluation performs an effect first (R13.3): <c>Prelude</c> runs,
/// then <c>Value</c> is the result. Produced only by an increment or decrement in
/// expression position, and never appears in a specification.
///
/// The effect is deliberately left <em>here</em>, at the operator's own position in the
/// tree, rather than hoisted to the front of the enclosing statement. Emit already walks
/// operands left to right and already captures the right operand of a short-circuit into
/// a conditional sub-block (R6.3), so leaving the effect in place makes it inherit C#'s
/// evaluation order and its conditional evaluation for free. Hoisting would have had to
/// reconstruct both, and would have been wrong for <c>p &amp;&amp; a[i++] &gt; 0</c>.
/// </summary>
public sealed record IrStmtExpr(
    IrLoc Loc, ImmutableArray<IrStmt> Prelude, IrExpr Value) : IrExpr(Loc);

// --- spec-only expression forms -------------------------------------------

/// <summary><c>Pal.Old(e)</c> — the value of <c>e</c> in the pre-state.</summary>
public sealed record IrOld(IrLoc Loc, IrExpr Operand) : IrExpr(Loc);

/// <summary><c>Pal.Result&lt;T&gt;()</c> / bare <c>return</c> in an <c>[Ensures]</c>.</summary>
public sealed record IrResult(IrLoc Loc) : IrExpr(Loc);

/// <summary>
/// R28.3. The reference a class-typed parameter holds, where a specification otherwise
/// reads the parameter as its model: <c>ReferenceEquals(Result._list, @this)</c>.
/// </summary>
public sealed record IrRefOf(IrLoc Loc, string Parameter) : IrExpr(Loc);

/// <summary><c>Pal.Live(x)</c> — an explicit ownership assertion.</summary>
public sealed record IrLive(IrLoc Loc, IrExpr Operand) : IrExpr(Loc);

public sealed record IrBinder(string Name, IrType Type);

public sealed record IrQuantifier(
    IrLoc Loc, bool IsForall, ImmutableArray<IrBinder> Binders, IrExpr Body) : IrExpr(Loc);

/// <summary>
/// <c>new T[n]</c> (R6.9). Executable only: an array is a resource, so it has no meaning
/// in a specification.
/// </summary>
public sealed record IrNewArray(IrLoc Loc, IrType Element, IrExpr Length) : IrExpr(Loc)
{
    /// <summary>
    /// R23.4. The array whose contents the new one starts with (<c>Array.Resize</c>): its
    /// first <c>min(length, n)</c> cells are copied and the rest are <c>default(T)</c>.
    /// </summary>
    public IrExpr? Source { get; init; }
}

/// <summary>R20.3. The operations of <c>Nullable&lt;T&gt;</c>.</summary>
public enum OptionOpKind { HasValue, Value, Some }

public sealed record IrOptionOp(IrLoc Loc, OptionOpKind Op, IrExpr Operand) : IrExpr(Loc);

/// <summary>
/// R21.7. <c>throw e</c> in expression position — a switch arm, a conditional branch. It
/// has whatever type its context wants and never yields a value.
/// </summary>
public sealed record IrRaise(IrLoc Loc, IrExpr Exception) : IrExpr(Loc);

/// <summary>R20.3. A method group converted to a delegate: <c>Type.Method</c>.</summary>
public sealed record IrMethodGroup(IrLoc Loc, string Method) : IrExpr(Loc);

/// <summary>
/// R20.6. <c>src.OrderBy(x =&gt; x.P).ToList()</c>: a fresh array holding the source's
/// elements stably sorted by the specification operation <paramref name="Key"/>.
/// </summary>
public sealed record IrOrderBy(IrLoc Loc, IrExpr Source, string Key, IrType KeyType) : IrExpr(Loc);

/// <summary><c>Pal.Contents(a)</c> — the ghost <c>Seq</c> view of an array.</summary>
public sealed record IrContents(IrLoc Loc, IrExpr Array) : IrExpr(Loc);

public enum SeqOpKind { Length, Index, SetAt, Slice, Splice, Rotate, IsPermutation, Snoc, Concat, Empty, Reverse }

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

public sealed record IrBlock(IrLoc Loc, ImmutableArray<IrStmt> Statements) : IrStmt(Loc)
{
    /// <summary>R26.2. Statements the lowerer produced for one, spliced into the enclosing block.</summary>
    public bool Splice { get; init; }
}

public sealed record IrLocalDecl(IrLoc Loc, string Name, IrType Type, IrExpr? Init) : IrStmt(Loc)
{
    /// <summary>
    /// Set on R13.3's snapshot of an incremented variable. Such a binding is written
    /// once and read once, so it is an immutable <c>let</c> rather than R5.2's cell —
    /// and, more to the point, it must be: a cell is a resource, and a resource declared
    /// inside a loop body would be carried into the ambient context of every enclosing
    /// block, where its name is out of scope.
    /// </summary>
    public bool Immutable { get; init; }

    /// <summary>
    /// R30.33. The local takes the array the field <see cref="Init"/> names, from the
    /// assignment that immediately follows and replaces it: that assignment hands the old
    /// array's ownership to the local instead of discarding it.
    /// </summary>
    public bool TakesField { get; init; }

    /// <summary>
    /// R27.41. A borrowing struct held in a local: for each object it owns, the field that
    /// holds it, the local the object is held in, and its class.
    /// </summary>
    public ImmutableArray<(string Field, string Local, IrClassType Type)> Owned { get; init; } = [];

    /// <summary>R27.49. For a borrowing struct held of another object of the class: that object's parameter.</summary>
    public string? HeldOwner { get; init; }
}

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
    IrStmt Body) : IrStmt(Loc)
{
}

/// <summary>
/// One section of a <c>switch</c>: the labels that select it and the statements it runs.
/// An empty <see cref="Labels"/> is the <c>default</c> section.
/// </summary>
public sealed record IrSwitchSection(
    IrLoc Loc,
    ImmutableArray<IrExpr> Labels,
    ImmutableArray<IrStmt> Statements);

/// <summary>
/// A <c>switch</c> statement, kept intact by lowering and desugared to a chain of
/// <see cref="IrIf"/> by the Normalize pass (R5.14).
/// </summary>
/// <param name="Scrutinee">
/// The immutable binding of the governing expression, which C# evaluates exactly once
/// however many arms the chain has. It is carried here rather than emitted beside the
/// <c>switch</c> so that the expansion can be spliced into its enclosing block: a
/// <c>switch</c> whose sections <c>return</c> becomes a chain of guards, and R5.5b can
/// only absorb what follows a chain if the chain is the block's own statement.
/// </param>
public sealed record IrSwitch(
    IrLoc Loc,
    IrLocalDecl Scrutinee,
    ImmutableArray<IrSwitchSection> Sections) : IrStmt(Loc);

public sealed record IrReturn(IrLoc Loc, IrExpr? Value) : IrStmt(Loc);

public sealed record IrExprStmt(IrLoc Loc, IrExpr Expr) : IrStmt(Loc);

/// <summary>R22.20, R22.25. A bulk operation of <c>System.Array</c>; its arguments, by kind:</summary>
/// <list type="bullet">
/// <item><c>Copy</c>: <c>src, dst, len</c> -- <c>Array.Copy(src, dst, len)</c>.</item>
/// <item><c>CopyAt</c>: <c>src, si, dst, di, len</c>, between distinct arrays.</item>
/// <item><c>Move</c>: <c>a, si, di, len</c> -- the same, within one array.</item>
/// <item><c>Clear</c>, <c>Reverse</c>: <c>a, i, n</c>.</item>
/// <item><c>Sort</c>: <c>a, i, n, comparer</c> (R26.7).</item>
/// </list>
public enum ArrayOpKind { Copy, CopyAt, Move, Clear, Reverse, Sort }

public sealed record IrArrayOp(IrLoc Loc, ArrayOpKind Op, ImmutableArray<IrExpr> Args) : IrStmt(Loc)
{
    /// <summary>The array the operation writes.</summary>
    public IrExpr Written => Op switch
    {
        ArrayOpKind.Copy => Args[1],
        ArrayOpKind.CopyAt => Args[2],
        _ => Args[0],
    };
}

/// <summary>
/// R22.25. <c>Array.IndexOf(a, x, i, n)</c>, or with <see cref="Last"/>
/// <c>Array.LastIndexOf(a, x, index, count)</c>: a read of <c>a</c> that yields a position.
/// </summary>
public sealed record IrArraySearch(IrLoc Loc, bool Last, IrExpr Array, IrExpr Item, IrExpr Start, IrExpr Count)
    : IrExpr(Loc);

/// <summary>
/// R25.5. <c>Array.BinarySearch(a, index, length, value, comparer)</c>: a read of <c>a</c>
/// that yields a position, or the complement of one.
/// </summary>
public sealed record IrArrayBinarySearch(IrLoc Loc, IrExpr Array, IrExpr Start, IrExpr Count, IrExpr Item, IrExpr Comparer)
    : IrExpr(Loc);

public sealed record IrBreak(IrLoc Loc) : IrStmt(Loc)
{
    /// <summary>R26.2. The <c>break</c> a <c>return</c> inside a loop was rewritten to.</summary>
    public bool FromReturn { get; init; }
}

public sealed record IrContinue(IrLoc Loc) : IrStmt(Loc);

public enum GhostKind { Assert, Assume, Raw, LemmaCall, Share, Gather, Restore, Let, Unreachable }

/// <summary>R19.3. <c>throw e;</c>, or <c>throw;</c> (a rethrow) when <see cref="Value"/> is null.</summary>
public sealed record IrThrow(IrLoc Loc, IrExpr? Value) : IrStmt(Loc);

/// <summary>
/// R19.4. One <c>catch</c> clause. <see cref="Type"/> is the exception type it selects
/// (<c>IrExnType(null)</c> for <c>catch</c> or <c>catch (Exception)</c>); <see cref="Var"/>
/// its binder, if any; <see cref="When"/> its filter.
/// </summary>
public sealed record IrCatch(IrLoc Loc, IrExnType Type, string? Var, IrExpr? When, IrBlock Body);

/// <summary>
/// R19.4. <c>try { … } catch …</c>. A Pulse <c>try</c> is not framed (F86): its
/// contract must own every slot in scope, so <see cref="Live"/> is every local and
/// parameter in scope, not only those mentioned, and <see cref="Unassigned"/> those the
/// try never assigns, whose values its contract keeps.
/// </summary>
public sealed record IrTry(IrLoc Loc, IrBlock Body, ImmutableArray<IrCatch> Catches) : IrStmt(Loc)
{
    /// <summary>
    /// R19.5. The leading <c>Pal.Invariant</c>s of the body: what holds wherever control
    /// leaves the body — at its end, and at every raise that reaches a handler — and at
    /// the end of each handler.
    /// </summary>
    public ImmutableArray<IrExpr> Invariants { get; init; } = [];

    public ImmutableArray<string> Live { get; init; } = [];
    public ImmutableArray<string> Unassigned { get; init; } = [];
}

/// <summary><c>Pal.Assert</c> / <c>Pal.Assume</c> / <c>Pal.GhostStmt</c> / <c>Pal.Share</c> /
/// <c>Pal.Gather</c> / a <c>[Lemma]</c> call.</summary>
public sealed record IrGhostStmt(IrLoc Loc, GhostKind Kind, IrExpr? Prop, string? Text) : IrStmt(Loc)
{
    /// <summary>R24.12. For <see cref="GhostKind.Let"/>, the ghost local's type.</summary>
    public IrType? Type { get; init; }
}

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
    /// <summary>R20.12. Stands for a readonly receiver field, so it is never written.</summary>
    public bool IsContext { get; init; }
    /// <summary>Ownership is transferred to the callee (<c>[Consumes]</c>).</summary>
    public bool Consumes { get; init; }
    /// <summary>Passed by value with no resource (<c>[Plain]</c>).</summary>
    public bool Plain { get; init; }
    /// <summary>Fractional-permission variable name (<c>[Frac("p")]</c>), if any.</summary>
    public string? Fraction { get; init; }
    /// <summary>R27.39. A <c>[Callback]</c> delegate parameter.</summary>
    public IrCallback? Callback { get; init; }
    /// <summary>R27.39. A ghost parameter passed explicitly (a lifted lambda's trace and ghost captures).</summary>
    public bool ExplicitGhost { get; init; }
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

    /// <summary>
    /// R27.42. An iterator method: its body is one whole enumeration, and it returns the
    /// sequence of the values it yields — a specification value, which no verified code
    /// receives, since calls to iterators are refused.
    /// </summary>
    public bool IsIterator { get; init; }
    /// <summary>R27.39. Set on a lambda lifted from a <c>[Callback]</c> argument.</summary>
    public IrLambdaInfo? Lambda { get; init; }
    public string? PulseBody { get; init; }

    /// <summary>
    /// R19.2. The method's <c>[Throws]</c> clauses. Empty means it must not throw: no
    /// <c>raises</c> clause is emitted, and Pulse then requires every exception the body
    /// could propagate to be proved impossible.
    /// </summary>
    public ImmutableArray<IrThrows> Throws { get; init; } = [];

    /// <summary>
    /// R27.57. <c>[Throws(..., At = typeof(S))]</c> clauses: each belongs to the replica of
    /// this method verified at the representation-sharing subclass <c>S</c>, by class name.
    /// </summary>
    public ImmutableArray<(string At, IrThrows Throws)> AtThrows { get; init; } = [];

    /// <summary>
    /// R14.2. The method's type parameters, in declaration order. They become explicit
    /// <c>Type0</c> binders ahead of every value parameter.
    /// </summary>
    public ImmutableArray<string> TypeParameters { get; init; } = ImmutableArray<string>.Empty;

    /// <summary>
    /// R14.2a. The type parameters the body takes <c>default</c> at. Each is a
    /// <c>has_default</c> obligation on the caller, bound after the type binders.
    /// </summary>
    public ImmutableArray<string> DefaultedTypeParameters { get; init; } = [];
    public bool Admit { get; init; }
    /// <summary>R22.31. The method's `[Rlimit]` factor, if any.</summary>
    public int? RlimitFactor { get; init; }
    /// <summary>R27.23. <c>[Open]</c>: the receiver is held as its record and heaps, not its invariant.</summary>
    public bool Open { get; init; }
    /// <summary>Expressions this method preserves (<c>[Preserves]</c>).</summary>
    public ImmutableArray<IrExpr> Preserves { get; init; } = ImmutableArray<IrExpr>.Empty;
    /// <summary>
    /// R27.37. How many leading <see cref="Ensures"/> are well typed and hold without the
    /// precondition (a borrowing member's frame facts), and so are stated unconditionally
    /// rather than under R4.8's <c>PRE ==&gt; POST</c>.
    /// </summary>
    public int UnconditionalEnsures { get; init; }

    /// <summary>
    /// The class this is an instance member of, if any (§4.5). A non-null value is what
    /// makes the emitter thread a model binder and bracket the body with
    /// <c>unfold</c>/<c>fold</c>.
    /// </summary>
    public string? DeclaringClass { get; init; }

    /// <summary>A constructor: it allocates and establishes the invariant (R4.12).</summary>
    public bool IsConstructor { get; init; }

    /// <summary>
    /// R9.21a. The generated leaf a constructor of an open class actually allocates. Its
    /// <see cref="ReturnType"/> stays the class the user named, so every <c>new C(…)</c> in
    /// the program is untouched and correctly typed; this says what the allocation builds,
    /// and the emitter upcasts once before returning.
    /// </summary>
    public string? ConstructsLeaf { get; init; }

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
    /// <summary>R24.17. A verbatim F* definition, replacing <see cref="Body"/>.</summary>
    public string? PulseBody { get; init; }

    /// <summary>R14.2: type binders, ahead of every value binder.</summary>
    public ImmutableArray<string> TypeParameters { get; init; } = [];

    public bool IsRecursive { get; init; }
    public IrExpr? Decreases { get; init; }
}

public sealed record IrFieldDecl(IrLoc Loc, string Name, IrType Type)
{
    /// <summary>R10.10. A back pointer: constrained by the invariant, not owned by it.</summary>
    public bool IsBackward { get; init; }

    /// <summary>
    /// R24.7. An array field declared <c>T[]?</c>: the class owns it through
    /// <c>Pulse.Lib.CSharp.NullableArray.pts_to</c>, which owns nothing when it is null.
    /// </summary>
    public bool IsNullableArray { get; init; }

    /// <summary>
    /// R27.37. A borrowing struct's field that owns an object: the record holds the box, and
    /// whoever holds the struct holds the object's invariant alongside it.
    /// </summary>
    public bool IsOwned { get; init; }
}

/// <summary>One argument of a recursive class's model constructor (R10.5).</summary>
public abstract record IrRecArg;

/// <summary>An argument that is a pure expression over the non-recursive fields.</summary>
public sealed record IrRecPure(IrExpr Value) : IrRecArg;

/// <summary>An argument that is a recursive field's own model, <c>f.M</c>.</summary>
public sealed record IrRecField(string Field) : IrRecArg;

/// <summary>Which inductive spec type a recursive class is modelled by (R10.5).</summary>
/// <summary>
/// R11.5. The two constructors of a recursive class's model type, as F* names. This is
/// everything §10's emitter ever needed about a model type, and replaces the enum of
/// built-in shapes it used to branch on.
///
/// <para>Both names are written in <em>prefix</em> form, including F*'s own <c>Nil</c> and
/// <c>Cons</c> (F44), so that one template serves a built-in model type and a user's
/// alike.</para>
/// </summary>
public sealed record IrModelShape(string Empty, string Cons)
{
    /// <summary>
    /// The discriminator of the non-empty constructor. Derived rather than declared: the
    /// trailing <c>?</c> is F*'s rule for every inductive, not ours.
    /// </summary>
    public string ConsTest => $"{Cons}?";
}

/// <summary>
/// R10.5. The induction the emitter reads off a recursive class's <c>[Model]</c> member:
/// the constructor's arguments, in order, each either pure or a recursive field. This is
/// the whole of what §10 extracts from the user's notation — the predicate, the six case
/// lemmas and the recursive share/gather are all functions of it.
/// </summary>
public sealed record IrRecursion(
    IrModelShape Shape,
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
    /// <summary>R15.1. The struct's own type parameters, in declaration order.</summary>
    public ImmutableArray<string> TypeParameters { get; init; } = [];

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
    /// <summary>R15.1. The class's own type parameters, in declaration order.</summary>
    public ImmutableArray<string> TypeParameters { get; init; } = [];

    /// <summary>
    /// R12.1. <c>[Plain]</c>: the class carries no derived ownership. Only its
    /// representation is emitted — no model type, no invariant, no case lemmas — and no
    /// contract mentioning it gains an automatic conjunct. Whatever owns its cells is
    /// said by the user, in a predicate the user also wrote.
    /// </summary>
    public bool IsPlain { get; init; }

    /// <summary>
    /// R27.3. <c>[Region]</c>: a plain class whose objects an owner holds as one region.
    /// <see cref="ModelBody"/>, when present, is the view of one node (R27.7), and the
    /// first two nullable fields of the class's own type are the children.
    /// </summary>
    public bool IsRegion { get; init; }

    /// <summary>
    /// R31.1. <c>[Region(Cyclic = true)]</c>: the two self-typed fields are ring links, not
    /// children, so no tree shape is derived for the region.
    /// </summary>
    public bool IsCyclic { get; init; }

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
    /// R9.21. The class is concrete but not <c>sealed</c>: it is both a vtable value and a
    /// vtable type, and <see cref="OpenClasses"/> splits it into the two halves §9 already
    /// translates before anything downstream sees it. No <see cref="IrClass"/> reaching the
    /// emitter has this set.
    /// </summary>
    public bool IsOpen { get; init; }

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
/// <summary>R19.2. One <c>[Throws(typeof(E), "when")]</c>: <see cref="When"/> may name <c>Thrown</c>.</summary>
public sealed record IrThrows(IrLoc Loc, IrExnType Type, IrExpr? When);

/// <summary>
/// R19.1. An exception class declared in the program. <see cref="Fields"/> are all its
/// fields, inherited ones first; <see cref="Ctor"/> the constructor's parameters and
/// <see cref="Inits"/> the value each field receives, over those parameters. A class
/// with no constructor of its own (an abstract base) has <see cref="Ctor"/> null.
/// </summary>
public sealed record IrException(
    IrLoc Loc,
    string Name,
    string? Base,
    ImmutableArray<IrFieldDecl> Fields,
    ImmutableArray<IrParam>? Ctor,
    ImmutableArray<IrExpr> Inits) : IrDecl(Loc, Name)
{
    public bool IsAbstract { get; init; }
}

public sealed record IrIncludePulse(IrLoc Loc, string Module, string Text) : IrDecl(Loc, Module);

/// <summary>The whole translation unit.</summary>
public sealed record IrProgram(ImmutableArray<IrDecl> Declarations);
