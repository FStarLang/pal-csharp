using System.Collections.Immutable;
using Pal.Compiler.Diagnostics;
using Pal.Compiler.Ir;

namespace Pal.Compiler.Emit;

/// <summary>
/// The Pulse terms a specification's free names denote, in one particular state.
/// A precondition, a postcondition, a loop invariant and a <c>decreases</c> measure
/// differ <em>only</em> in this environment; the translation of the expression itself
/// is the same in all four.
/// </summary>
public sealed class SpecScope
{
    private readonly Dictionary<string, Term> _values = [];

    public SpecScope? Pre { get; init; }
    public string? ResultTerm { get; init; }

    /// <summary>
    /// The class whose module this specification is being emitted into, if any. An
    /// observation of *that* class is then written unqualified (R3.7).
    /// </summary>
    public string? DefiningClass { get; init; }

    /// <summary>
    /// What kind of value <c>Result</c> denotes. A method's result is a machine value,
    /// but a <c>[Refine]</c> on a <c>[Model]</c> member names the *model* (R3.9d), which
    /// is a ghost value and carries no <c>Int32.v</c>.
    /// </summary>
    public TermKind ResultKind { get; init; } = TermKind.Machine;

    /// <summary>
    /// The declared type <c>Result</c> denotes, when the emitter knows it. A specification
    /// string is bound in a shim that erases nullable annotations, so the type on an
    /// <c>IrResult</c> node cannot tell <c>C</c> from <c>C?</c>; this can, and R10.2b needs
    /// the difference.
    /// </summary>
    public IrType? ResultType { get; init; }

    public SpecScope() { }

    public SpecScope(SpecScope other)
    {
        _values = new Dictionary<string, Term>(other._values);
        Pre = other.Pre;
        ResultTerm = other.ResultTerm;
        DefiningClass = other.DefiningClass;
        ResultKind = other.ResultKind;
        ResultType = other.ResultType;
    }

    public void Bind(string name, Term term) => _values[name] = term;

    public bool TryGet(string name, out Term term) => _values.TryGetValue(name, out term);

    public SpecScope With(string name, Term term)
    {
        var copy = new SpecScope(this);
        copy.Bind(name, term);
        return copy;
    }
}

/// <summary>
/// Translates an <see cref="IrExpr"/> in specification position (doc/translation.md §6).
///
/// <para>
/// In spec position arithmetic is mathematical: a C# <c>int</c> denotes its
/// <c>Int32.v</c> value, so a specification never carries the overflow obligations that
/// the corresponding <em>code</em> carries. That is what makes
/// <c>Sorted(a, 0, a.Length)</c> mean what a reader expects.
/// </para>
/// </summary>
public sealed class SpecEmitter(DiagnosticBag diagnostics)
{
    /// <summary>
    /// R9.19. Each class's immediate base, which is what <see cref="Forget"/> walks.
    /// Set once per program; empty for a program with no hierarchy.
    /// </summary>
    public IReadOnlyDictionary<string, string> Bases { get; set; } =
        new Dictionary<string, string>();

    /// <summary>
    /// R9.19. An observation declared on an ancestor, read off a descendant's model.
    ///
    /// <para>The receiver's term denotes a model of *some* class in the hierarchy — which
    /// one is recorded on the term, and it is not always the class the <c>[Spec]</c> member
    /// belongs to. A client may write <c>q.TheArea</c> where <c>TheArea</c> is
    /// <c>Shape</c>'s and <c>q</c> is a <c>Quadrilateral</c>; and R9.7's inherited contract
    /// is written against the base's model and then re-read at the model of whichever class
    /// the <c>override</c>'s vtable slot is typed at, which at depth three is neither the
    /// declaring class nor the implementing one.</para>
    ///
    /// <para>Both are the same step, so there is one rule: compose the forgetting functions
    /// R9.6 already emits, from the class the term denotes up to the class that declares
    /// the member. The chain is walked and not guessed; a member the receiver's class does
    /// not inherit is a C# error the frontend has already refused.</para>
    /// </summary>
    private string Forget(IrObserve ob, Term receiver, SpecScope scope)
    {
        if (receiver.Type is not IrClassType from) return receiver.Text;
        var text = receiver.Text;
        for (var at = from.Name; at != ob.Class && Bases.TryGetValue(at, out var up); at = up)
        {
            var qualifier = scope.DefiningClass == at ? "" : Names.ClassModule(at) + ".";
            text = $"({qualifier}{Names.ClassForget(at)} {text})";
        }
        return text;
    }

    public Term Emit(IrExpr expr, SpecScope scope)
    {
        switch (expr)
        {
            case IrLiteral l:
                return l.Value switch
                {
                    bool b => new Term(b ? "True" : "False", TermKind.Prop),
                    // R20.3. Strings and decimals are values, not numbers.
                    string or decimal => new Term(Types.Literal(l.Value, l.Type), TermKind.Other, l.Type),
                    _ => new Term(Render(l.Value), TermKind.Math),
                };

            // R20.3. `T?` is `option T`, with the same reading as in code.
            case IrNull { Type: IrOptionType on }:
                return new Term($"(None #{Types.Atom(on.Inner)})", TermKind.Other, on);
            case IrOptionOp oo:
            {
                var operand = Emit(oo.Operand, scope).Text;
                return oo.Op switch
                {
                    OptionOpKind.HasValue => new Term($"(Some? {operand})", TermKind.Bool, IrPrim.Bool),
                    OptionOpKind.Value => new Term($"(Some?.v {operand})",
                        MethodPlan.KindOf(oo.Type ?? IrPrim.Int), oo.Type),
                    _ => new Term($"(Some {operand})", TermKind.Other, oo.Type),
                };
            }
            case IrMethodGroup mg:
                return new Term($"(Opaque.method_group {Types.StringLiteral(mg.Method)})", TermKind.Other, mg.Type);

            case IrVar v when scope.TryGet(v.Name, out var bound):
                return bound;

            case IrVar v:
                diagnostics.Error("PALCS0300", v.Loc,
                    $"`{v.Name}` cannot be mentioned in this specification.");
                return new Term("()", TermKind.Other);

            // R3.9c: an observation is the class's spec function applied to the *model*
            // the receiver denotes in this state. `Old(@this.X)` therefore needs no new
            // machinery: it is this same case emitted in the pre-state scope.
            case IrObserve ob:
            {
                var receiver = Emit(ob.Receiver, scope);
                // R3.7's rule about field qualifiers applies to observations too: inside
                // the class's own module the qualifier is not merely redundant, it makes
                // F*'s dependency scan read the module as depending on itself.
                var qualifier = scope.DefiningClass == ob.Class
                    ? "" : Names.ClassModule(ob.Class) + ".";
                return new Term(
                    $"({qualifier}{Names.Observation(ob.Class, ob.Member)} {Forget(ob, receiver, scope)})",
                    MethodPlan.KindOf(ob.Type ?? IrPrim.Bool), ob.Type);
            }

            case IrOld o when scope.Pre is { } pre:
                return Emit(o.Operand, pre);

            case IrOld o:
                diagnostics.Error("PALCS0301", o.Loc,
                    "`Pal.Old` is only meaningful in a postcondition or a loop invariant.");
                return new Term("()", TermKind.Other);

            case IrResult r when scope.ResultTerm is { } result:
                return new Term(result, scope.ResultKind, scope.ResultType ?? r.Type);

            case IrResult r:
                diagnostics.Error("PALCS0302", r.Loc, "`Pal.Result` is only meaningful in a postcondition.");
                return new Term("()", TermKind.Other);

            case IrUnary u:
                return Unary(u, scope);

            case IrBinary bin:
                return Binary(bin, scope);

            case IrConditional c:
            {
                var then = Emit(c.Then, scope);
                return new Term(
                    $"(if {Bool(c.Cond, scope)} then {AsMath(then)} else {Math(c.Else, scope)})",
                    then.Kind == TermKind.Seq ? TermKind.Seq : TermKind.Math);
            }

            case IrContents ct:
                return Emit(ct.Array, scope) with { Kind = TermKind.Seq };

            case IrLength len:
            {
                // F7. `a.Length` has two readings: in a specification the array is
                // represented by its contents, so it is `Seq.length`; in a termination
                // measure only the live array is in scope, and its length is the pure
                // `arr_length`, which is exactly what F7 introduced it for. The reading is
                // chosen by what the array term denotes, never by where we happen to be.
                var arr = Emit(len.Array, scope);
                return arr.Kind == TermKind.Array
                    ? new Term($"(arr_length {arr.Text})", TermKind.Machine, IrPrim.Int)
                    : new Term($"(Seq.length {arr.Text})", TermKind.Math);
            }

            case IrElement el:
            {
                var arr = Emit(el.Array, scope);
                if (arr.Kind == TermKind.Array)
                {
                    diagnostics.Error("PALCS0304", el.Loc,
                        "An array element cannot be read here: only the array itself is in " +
                        "scope, not its contents. Name the value in a loop invariant first.");
                    return new Term("()", TermKind.Other);
                }
                return new Term(
                    $"(Seq.index {arr.Text} {Math(el.Index, scope)})",
                    el.Type is null ? TermKind.Machine : MethodPlan.KindOf(el.Type), el.Type);
            }

            case IrSeqOp s:
                return SeqOp(s, scope);

            case IrListOp l:
                return ListOp(l, scope);

            case IrSpecOp o:
                return SpecOp(o, scope);

            // R10.2. `null` is `B.null`. The type annotation is what lets F* infer the
            // box's parameter in `pure (x == B.null)` positions where nothing else
            // determines it — and it is the *representation* the box is of, since
            // `class_C__opt` is `B.box class_C__raw`.
            case IrNull n:
                return new Term(
                    n.Type is IrClassType nullClass
                        ? "(B.null #" + Types.Applied(
                              $"{Names.ClassModule(nullClass.Name)}.{Names.ClassRaw(nullClass.Name)}",
                              nullClass.TypeArguments) + ")"
                        : "B.null",
                    TermKind.Other);

            // R5.12. Inside R4.10's window the receiver is a representation, and a loop
            // invariant naming a field means that representation's field. The binding is
            // put there by the loop emitter, which is the only place that knows the
            // record's name; here it is an ordinary lookup.
            case IrField { Receiver: IrVar { Name: Names.This } } tf
                when scope.TryGet($"{Names.This}.{tf.Field}", out var repField):
                return repField;

            case IrField { Receiver.Type: IrClassType oc } cf:
                diagnostics.Unsupported(cf.Loc,
                    $"The field `{cf.Field}` in this specification",
                    $"A field of `{oc.Name}` can be named in a loop invariant inside the " +
                    "class's own instance method, where R4.10 has the representation open. " +
                    "In a contract, name a `[Spec]` observation instead — a caller holds " +
                    "the model, not the fields (R3.9c).");
                return new Term("()", TermKind.Other);

            // R19.1. An exception's field is read through its class's accessor, which has
            // a case for every subclass, so the field means the same whatever was thrown.
            case IrField { Receiver.Type: IrExnType { Name: { } en } } ef:
                return new Term(
                    $"({Names.Qualified(Names.ExnField(en, ef.Field))} {Emit(ef.Receiver, scope).Text})",
                    MethodPlan.KindOf(ef.Type ?? IrPrim.Int), ef.Type);

            case IrField f:
            {
                // R3.5. The struct name comes from the receiver's C# type, which is what
                // makes the projection module-qualified (F10) and so unambiguous.
                var receiver = Emit(f.Receiver, scope);
                if ((f.Receiver.Type ?? receiver.Type) is not IrNamedType named)
                {
                    diagnostics.Unsupported(f.Loc, $"The field access `.{f.Field}`");
                    return new Term("()", TermKind.Other);
                }
                return new Term(
                    $"{Receiver(receiver.Text)}.{Names.Projection(named.Name, f.Field)}",
                    MethodPlan.KindOf(f.Type ?? IrPrim.Int), f.Type);
            }

            case IrNew n:
                return new Term(
                    "({ " + string.Join("; ", n.Fields.Select((f, i) =>
                        (i == 0 ? Names.Projection(n.Struct, f.Field) : Names.Field(f.Field))
                        + " = " + FieldValue(f.Value, f.FieldType, scope))) + " })",
                    TermKind.Other, n.Type);

            case IrQuantifier q:
                return Quantifier(q, scope);

            case IrCall { Kind: CalleeKind.Spec } call:
                // R4.6: a [Spec] function returning `bool` denotes a proposition; one
                // returning an integer denotes a mathematical value, and so may be used
                // in arithmetic and as an array index.
                // R14.5. A generic [Spec] function is applied to its type arguments first,
                // exactly as a generic method is: a specification is emitted from the same
                // IR call node and has no reason to differ.
                return new Term(
                    $"({Names.SpecFunction(call.Callee)} " +
                    string.Join(" ", call.TypeArguments.Select(Types.Atom)
                        .Concat(call.Args.Select((a, i) => Argument(a, ParamType(call, i), scope)))) + ")",
                    call.ResultType is IrPrim { IsMachineInt: true } ? TermKind.Math : TermKind.Prop,
                    call.ResultType);

            case IrConvert cv:
                // R13.2. A conversion is the identity on mathematical values exactly when
                // every value of the source type is a value of the target — which is a
                // narrower condition than "widening", since `uint -> int` and
                // `byte -> sbyte` both lose values without narrowing the width.
                //
                // When it does not fit, the specification has to say what the code does,
                // and what the code does is truncate (R13.1, F48). Reporting it as the
                // identity would let a user prove `(byte)300 == 300`.
                if (cv.Operand.Type is IrPrim { Kind: var src } && cv.Target is IrPrim { Kind: var dst }
                    && src != dst && !Types.RangeFits(src, dst))
                {
                    var v = Math(cv.Operand, scope);
                    var bits = Types.Width(dst);
                    // Two's complement: unsigned truncation is `%`, signed truncation is
                    // F*'s `@%`, which centres the residue on the signed range.
                    var text = Types.Signed(dst)
                        ? $"(FStar.Int.op_At_Percent {v} (pow2 {bits}))"
                        : $"({v} % pow2 {bits})";
                    return new Term(text, TermKind.Math, cv.Target);
                }
                // The value is unchanged, but its *type* is not, and a machine term still
                // carries the module whose `.v` reads it. Taking the mathematical value
                // here, at the source type, is what stops the target's module being
                // applied to the source's representation.
                var kept = Emit(cv.Operand, scope);
                return kept.Kind == TermKind.Machine
                    ? new Term(AsMath(kept), TermKind.Math, cv.Target)
                    : kept with { Type = cv.Target };

            case IrInlinePulse raw:
                return new Term($"({Antiquotation.Expand(raw.Text, scope)})", TermKind.Other);

            case IrLive live:
                diagnostics.Error("PALCS0303", live.Loc,
                    "`Pal.Live` describes ownership, so it cannot appear inside a pure specification.");
                return new Term("True", TermKind.Prop);

            case IrTypeBoundMeasure m:
                return TypeBoundMeasure(m, scope);

            default:
                diagnostics.Unsupported(expr.Loc, $"`{expr.GetType().Name}` in specification position");
                return new Term("()", TermKind.Other);
        }
    }

    private static string Render(object? value) => value switch
    {
        null => "()",
        bool b => b ? "true" : "false",
        _ => Convert.ToString(value, System.Globalization.CultureInfo.InvariantCulture) ?? "0",
    };

    /// <summary>Coerces a term to the mathematical integer a specification reasons about.</summary>
    public string Math(IrExpr expr, SpecScope scope) => AsMath(Emit(expr, scope));

    public string AsMath(Term term) => term.Kind switch
    {
        TermKind.Machine => $"({Types.Module((term.Type as IrPrim)?.Kind ?? PrimKind.Int)}.v {term.Text})",
        _ => term.Text,
    };

    /// <summary>Coerces a term to a proposition.</summary>
    public string AsProp(Term term) => term.Text;

    /// <summary>
    /// Renders an expression as a <em>decidable</em> boolean. A specification is
    /// otherwise translated into <c>prop</c>, where <c>==</c> and <c>/\</c> live; but the
    /// guard of a conditional has to be something F* can branch on, so equality becomes
    /// <c>=</c> and conjunction becomes <c>&amp;&amp;</c>.
    /// </summary>
    public string Bool(IrExpr expr, SpecScope scope)
    {
        switch (expr)
        {
            case IrUnary { Op: UnOp.Not } u:
                return $"(not {Bool(u.Operand, scope)})";

            case IrBinary b when DecimalOrder(b, scope) is { } ordered:
                return ordered;

            case IrBinary b:
            {
                var op = b.Op switch
                {
                    BinOp.Eq => "=", BinOp.Ne => "<>",
                    BinOp.Lt => "<", BinOp.Le => "<=", BinOp.Gt => ">", BinOp.Ge => ">=",
                    _ => null,
                };
                if (op is not null)
                    return $"({Math(b.Left, scope)} {op} {Math(b.Right, scope)})";
                if (b.Op is BinOp.And or BinOp.Or)
                    return $"({Bool(b.Left, scope)} {(b.Op == BinOp.And ? "&&" : "||")} {Bool(b.Right, scope)})";
                break;
            }

            case IrLiteral { Value: bool v }:
                return v ? "true" : "false";
        }

        return Emit(expr, scope).Text;
    }

    private Term Unary(IrUnary u, SpecScope scope) => u.Op switch
    {
        UnOp.Not => new Term($"(~ {AsProp(Emit(u.Operand, scope))})", TermKind.Prop),
        UnOp.Neg => new Term($"(0 - {Math(u.Operand, scope)})", TermKind.Math),

        // R6.4b, at a unary operator. `FStar.Int32.lognot` is specified as
        // `lognot (v x) == v z`, so naming `FStar.Int.lognot` on the operand's value says
        // what `~x` computes. Refused where there is no faithful image, for the reason
        // the arm below exists.
        UnOp.BitNot when Complement(u) is { } fn
            => new Term($"({fn} {Math(u.Operand, scope)})", TermKind.Math),

        // R6.4b. No catch-all. This arm used to return the operand *with the operator
        // dropped*, so `Result == ~(x + 1)` reached F* as `Result == x + 1` and a method
        // returning `x + 1` proved it — where C#'s `~(x + 1)` is `-(x + 2)`.
        _ => UnsupportedUnary(u),
    };

    /// <summary>
    /// R6.4b. The <c>FStar.Int</c>/<c>FStar.UInt</c> complement for a machine integer
    /// operand, or <c>null</c> where no faithful image exists.
    /// </summary>
    private static string? Complement(IrUnary u) =>
        u.Operand.Type is IrPrim { IsMachineInt: true } p
            ? $"{(p.IsSignedMachineInt ? "FStar.Int" : "FStar.UInt")}.lognot #{Types.Width(p.Kind)}"
            : null;

    private Term UnsupportedUnary(IrUnary u)
    {
        diagnostics.Unsupported(u.Loc, $"The operator `{(u.Op == UnOp.BitNot ? "~" : u.Op.ToString())}` in specification position");
        return new Term("0", TermKind.Math);
    }

    /// <summary>R20.3. A comparison of two decimals, as <c>Pulse.Lib.CSharp.Decimal</c>'s.</summary>
    private string? DecimalOrder(IrBinary b, SpecScope scope)
    {
        if (b.Left.Type is not IrPrim { Kind: PrimKind.Decimal }) return null;
        var fn = b.Op switch
        {
            BinOp.Lt => "D.lt", BinOp.Le => "D.le", BinOp.Gt => "D.gt", BinOp.Ge => "D.ge",
            _ => null,
        };
        return fn is null ? null : $"({fn} {Emit(b.Left, scope).Text} {Emit(b.Right, scope).Text})";
    }

    private Term Binary(IrBinary b, SpecScope scope)
    {
        string Infix(string op, TermKind kind, bool mathematical = true)
        {
            var left = mathematical ? Math(b.Left, scope) : AsProp(Emit(b.Left, scope));
            var right = mathematical ? Math(b.Right, scope) : AsProp(Emit(b.Right, scope));
            _ = kind;
            return $"({left} {op} {right})";
        }

        // An operator whose C# meaning is a library function rather than one of F*'s.
        string Prefix(string fn) => $"({fn} {Math(b.Left, scope)} {Math(b.Right, scope)})";

        // R6.4a. C#'s `/` and `%` round toward zero and F*'s round toward minus infinity,
        // so on a negative operand the two disagree: `-7 / 2` is `-3` in C# and `-4` in F*.
        // A specification that quotes a *C#* expression has to mean the C#, or the reader
        // and the prover read the same string differently — and that difference is
        // invisible, because it shows up only in a sign the reader was not thinking about.
        //
        // Two conditions have to hold before the divergence is even reachable. Both
        // operands must be machine integers, because a spec-only numeric has no runtime
        // existence and no C# operator to disagree with; there `/` and `%` are the
        // mathematics they look like. And one of them must be signed, because on
        // unsigned operands the two roundings coincide exactly. Where neither holds,
        // F*'s operators already *are* C#'s, and are left in place.
        static bool Machine(IrExpr e) => e.Type is IrPrim { IsMachineInt: true };
        static bool Signed(IrExpr e) => e.Type is IrPrim { IsSignedMachineInt: true };
        var quotesCSharp = Machine(b.Left) && Machine(b.Right)
            && (Signed(b.Left) || Signed(b.Right));

        if (DecimalOrder(b, scope) is { } ordered) return new Term(ordered, TermKind.Bool, IrPrim.Bool);
        if (b.Left.Type is IrPrim { Kind: PrimKind.Decimal or PrimKind.String } &&
            b.Op is not (BinOp.Eq or BinOp.Ne))
            return Unsupported(b);

        return b.Op switch
        {
            BinOp.Add => new Term(Infix("+", TermKind.Math), TermKind.Math),
            BinOp.Sub => new Term(Infix("-", TermKind.Math), TermKind.Math),
            BinOp.Mul => new Term(Infix("*", TermKind.Math), TermKind.Math),
            BinOp.Div => new Term(
                quotesCSharp ? Prefix("CA.cdiv") : Infix("/", TermKind.Math), TermKind.Math),
            BinOp.Rem => new Term(
                quotesCSharp ? Prefix("CA.crem") : Infix("%", TermKind.Math), TermKind.Math),
            BinOp.Lt => new Term(Infix("<", TermKind.Prop), TermKind.Prop),
            BinOp.Le => new Term(Infix("<=", TermKind.Prop), TermKind.Prop),
            BinOp.Gt => new Term(Infix(">", TermKind.Prop), TermKind.Prop),
            BinOp.Ge => new Term(Infix(">=", TermKind.Prop), TermKind.Prop),
            BinOp.Eq => new Term(Equality(b, scope, negated: false), TermKind.Prop),
            BinOp.Ne => new Term(Equality(b, scope, negated: true), TermKind.Prop),
            BinOp.And => new Term(Infix("/\\", TermKind.Prop, mathematical: false), TermKind.Prop),
            BinOp.Or => new Term(Infix("\\/", TermKind.Prop, mathematical: false), TermKind.Prop),
            BinOp.Implies => new Term(Infix("==>", TermKind.Prop, mathematical: false), TermKind.Prop),
            BinOp.Iff => new Term(Infix("<==>", TermKind.Prop, mathematical: false), TermKind.Prop),

            // R6.4b. A bitwise operator over machine integers is exactly what the code
            // emits: `FStar.Int32.logand a b` is specified as `v c == Int.logand (v a)
            // (v b)`, so naming `Int.logand` on the operands' values makes a contract
            // that quotes `a & b` say what `a & b` computes.
            BinOp.BitAnd or BinOp.BitOr or BinOp.BitXor when Bitwise(b) is { } fn
                => new Term(Prefix(fn), TermKind.Math),

            // R6.4b. Everything else in this family has no faithful image yet: a bitwise
            // operator over a spec-only numeric is bit manipulation of a number with no
            // width, and a shift is C#'s masked shift (§12.11: the count is taken mod 32
            // or 64), which F*'s `shift_left` does not model. §0 rule 3 — refuse what
            // cannot be translated rather than translate it into something else.
            BinOp.BitAnd or BinOp.BitOr or BinOp.BitXor or BinOp.Shl or BinOp.Shr
                => Unsupported(b),

            _ => Unsupported(b),
        };
    }

    /// <summary>
    /// R6.4b. The `FStar.Int`/`FStar.UInt` function a C# bitwise operator denotes, or
    /// `null` where no faithful image exists. Both operands must be machine integers of
    /// the same width and signedness: the operation is defined on `int_t n`, and the
    /// value a specification speaks of (`I32.v x`) is exactly that.
    /// </summary>
    private static string? Bitwise(IrBinary b)
    {
        if (b.Left.Type is not IrPrim { IsMachineInt: true } l ||
            b.Right.Type is not IrPrim { IsMachineInt: true } r ||
            l.Kind != r.Kind)
            return null;

        var module = l.IsSignedMachineInt ? "FStar.Int" : "FStar.UInt";
        var name = b.Op switch
        {
            BinOp.BitAnd => "logand",
            BinOp.BitOr => "logor",
            BinOp.BitXor => "logxor",
            _ => null,
        };
        return name is null ? null : $"{module}.{name} #{Types.Width(l.Kind)}";
    }

    /// <summary>
    /// R6.4b. An operator with no translation is refused, not approximated. This method
    /// exists because the alternative — a catch-all arm — is how `&` came to be emitted
    /// as `+`: a default that answers for operators it does not recognise gives a wrong
    /// answer silently, and a specification is the one place a wrong answer cannot be
    /// caught downstream, because the prover is checking the translation, not the C#.
    /// </summary>
    private Term Unsupported(IrBinary b)
    {
        var spelling = b.Op switch
        {
            BinOp.BitAnd => "&", BinOp.BitOr => "|", BinOp.BitXor => "^",
            BinOp.Shl => "<<", BinOp.Shr => ">>",
            _ => b.Op.ToString(),
        };
        diagnostics.Unsupported(b.Loc, $"The operator `{spelling}` in specification position");
        return new Term("0", TermKind.Math);
    }

    /// <summary>
    /// Equality is the one operator whose translation depends on the operands' kind:
    /// two sequences compare as sequences, two integers as mathematical integers.
    /// </summary>
    private string Equality(IrBinary b, SpecScope scope, bool negated)
    {
        var left = Emit(b.Left, scope);
        var right = Emit(b.Right, scope);
        // R10.2b, at an equality. C# lets a `C` be compared with a `C?`, and R10.2 makes
        // the two one type, so the comparison needs no widening.
        var comparable = left.Kind is TermKind.Seq or TermKind.Bool or TermKind.Prop or TermKind.Other;
        // R22.23. Two sequences are equal when they agree pointwise, and `Seq.equal` is
        // the form of that the solver can prove; `lemma_eq_elim`'s pattern turns it back
        // into `==` wherever it is assumed.
        // Only a sequence *built* by an operation is compared so: between two names the
        // quantifier `Seq.equal` unfolds to buys nothing and costs the solver.
        var text = left.Kind is TermKind.Seq && right.Kind is TermKind.Seq &&
                   (b.Left is IrSeqOp || b.Right is IrSeqOp)
            ? $"(Seq.equal {left.Text} {right.Text})"
            : comparable
            ? $"({left.Text} == {right.Text})"
            : $"({AsMath(left)} == {AsMath(right)})";
        return negated ? $"(~ {text})" : text;
    }

    private Term SeqOp(IrSeqOp s, SpecScope scope) => s.Op switch
    {
        SeqOpKind.Length => new Term($"(Seq.length {Emit(s.Args[0], scope).Text})", TermKind.Math),
        SeqOpKind.Index => new Term(
            $"(Seq.index {Emit(s.Args[0], scope).Text} {Math(s.Args[1], scope)})",
            ElementType(s.Args[0]) is { } et ? MethodPlan.KindOf(et) : TermKind.Machine, ElementType(s.Args[0])),
        SeqOpKind.SetAt => new Term(
            $"(Seq.upd {Emit(s.Args[0], scope).Text} {Math(s.Args[1], scope)} {Emit(s.Args[2], scope).Text})",
            TermKind.Seq),
        SeqOpKind.Slice => new Term(
            $"(Seq.slice {Emit(s.Args[0], scope).Text} {Math(s.Args[1], scope)} {Math(s.Args[2], scope)})",
            TermKind.Seq),
        SeqOpKind.Splice => new Term(
            $"(CS.splice {Emit(s.Args[0], scope).Text} {Math(s.Args[1], scope)} " +
            $"{Math(s.Args[2], scope)} {Emit(s.Args[3], scope).Text})",
            TermKind.Seq),
        SeqOpKind.Rotate => new Term(
            $"(CS.rotate {Emit(s.Args[0], scope).Text} {Math(s.Args[1], scope)})",
            TermKind.Seq),
        SeqOpKind.Snoc => new Term(
            $"(Seq.snoc {Emit(s.Args[0], scope).Text} {Emit(s.Args[1], scope).Text})", TermKind.Seq),
        SeqOpKind.Concat => new Term(
            $"(Seq.append {Emit(s.Args[0], scope).Text} {Emit(s.Args[1], scope).Text})", TermKind.Seq),
        SeqOpKind.Empty => new Term("Seq.empty", TermKind.Seq),
        SeqOpKind.IsPermutation => new Term(
            $"(CS.is_permutation {Emit(s.Args[0], scope).Text} {Emit(s.Args[1], scope).Text})",
            TermKind.Prop),
        // R6.4b. Every member of `SeqOpKind` is handled above, so this arm is
        // unreachable — and it says so rather than emitting `True`, which is what it used
        // to do. A `True` here would make a postcondition mentioning a new sequence
        // operation vacuous instead of wrong, which is the quieter failure and the harder
        // one to notice. An arm that cannot answer refuses.
        _ => UnsupportedOp(s.Loc, $"The sequence operation `{s.Op}`"),
    };

    /// <summary>R10.5. The ghost list, F*'s own <c>list</c> and <c>FStar.List.Tot</c>.</summary>
    private Term ListOp(IrListOp l, SpecScope scope) => l.Op switch
    {
        ListOpKind.Empty => new Term("[]", TermKind.Other),
        ListOpKind.Cons => new Term(
            $"({AsMath(Emit(l.Args[0], scope))} :: {Emit(l.Args[1], scope).Text})", TermKind.Other),
        ListOpKind.Append => new Term(
            $"(List.Tot.append {Emit(l.Args[0], scope).Text} {Emit(l.Args[1], scope).Text})",
            TermKind.Other),
        ListOpKind.Length => new Term(
            $"(List.Tot.length {Emit(l.Args[0], scope).Text})", TermKind.Math),
        ListOpKind.IsEmpty => new Term(
            $"(Nil? {Emit(l.Args[0], scope).Text})", TermKind.Prop),
        ListOpKind.Head => new Term(
            $"(List.Tot.hd {Emit(l.Args[0], scope).Text})", TermKind.Math),
        ListOpKind.Tail => new Term(
            $"(List.Tot.tl {Emit(l.Args[0], scope).Text})", TermKind.Other),
        ListOpKind.Index => new Term(
            $"(List.Tot.index {Emit(l.Args[0], scope).Text} {Math(l.Args[1], scope)})", TermKind.Math),
        // R15.7. `Pulse.Lib.CSharp.List` states each of these as a *total* function of an
        // `int`, so the term is well typed wherever a C# index is, with no side condition.
        ListOpKind.Take => new Term(
            $"(CL.take {Emit(l.Args[0], scope).Text} {Math(l.Args[1], scope)})", TermKind.Other),
        ListOpKind.Drop => new Term(
            $"(CL.drop {Emit(l.Args[0], scope).Text} {Math(l.Args[1], scope)})", TermKind.Other),
        ListOpKind.InsertAt => new Term(
            $"(CL.insert_at {Emit(l.Args[0], scope).Text} {Math(l.Args[1], scope)} " +
            $"{AsMath(Emit(l.Args[2], scope))})", TermKind.Other),
        ListOpKind.RemoveAt => new Term(
            $"(CL.remove_at {Emit(l.Args[0], scope).Text} {Math(l.Args[1], scope)})", TermKind.Other),
        ListOpKind.Reverse => new Term(
            $"(CL.rev {Emit(l.Args[0], scope).Text})", TermKind.Other),
        // R6.4b, as for `SeqOp` above: unreachable, and refusing rather than emitting a
        // vacuous `True` if it ever stops being so.
        _ => UnsupportedOp(l.Loc, $"The list operation `{l.Op}`"),
    };

    /// <summary>
    /// R6.4b. A spec-level operation with no emission is refused. Shared by the arms that
    /// are unreachable today, so that adding an enum member without adding its rule is a
    /// diagnostic rather than a silently different specification.
    /// </summary>
    private Term UnsupportedOp(IrLoc loc, string what)
    {
        diagnostics.Unsupported(loc, $"{what} in specification position");
        return new Term("True", TermKind.Prop);
    }

    /// <summary>
    /// R11.2. A user-declared specification operation: the F* term it named, applied to
    /// its arguments. There is nothing to decide — the name came from the user's
    /// <c>[SpecOp]</c> or <c>[SpecCtor]</c> and is emitted verbatim.
    ///
    /// <para>Every argument goes through <see cref="AsMath"/>, which is a no-op except on
    /// a machine integer: a specification type's arguments are mathematical, so an
    /// <c>Int32.t</c> in argument position needs <c>.v</c>. This is the same coercion the
    /// built-in operations applied, stated once.</para>
    ///
    /// <para>The result's <see cref="TermKind"/> is read off the member's C# return type
    /// rather than declared, because C# already says whether it is a number, a
    /// proposition or a structure.</para>
    /// </summary>
    private Term SpecOp(IrSpecOp op, SpecScope scope)
    {
        var operands = op.TypeArgs.Select(Types.Atom)
            .Concat(op.Args.Select((a, i) =>
                i < op.ParamTypes.Length && op.ParamTypes[i] is IrClassType
                    ? Argument(a, op.ParamTypes[i], scope)
                    : op.MachineArgs
                        ? a is IrLiteral { Value: not (null or bool or string or decimal) } l
                            ? Types.Literal(l.Value, l.Type)
                            : Emit(a, scope).Text
                        : AsMath(Emit(a, scope)))).ToList();
        var text = operands.Count == 0
            ? op.Function
            : $"({op.Function} {string.Join(" ", operands)})";
        return new Term(text, Kind(op.Type));
    }

    /// <summary>R11.2. What a specification type's member returns, as a term kind.</summary>
    private static TermKind Kind(IrType? type) => type switch
    {
        IrPrim { Kind: PrimKind.SpecInt or PrimKind.SpecNat } => TermKind.Math,
        IrPrim { Kind: PrimKind.Bool } => TermKind.Prop,
        IrSeqType => TermKind.Seq,
        _ => TermKind.Other,
    };

    private static IrType? ElementType(IrExpr sequence) => sequence.Type switch
    {
        IrSeqType s => s.Element,
        IrArrayType a => a.Element,
        IrSpanType a => a.Element,
        _ => null,
    };

    private Term Quantifier(IrQuantifier q, SpecScope scope)
    {
        // A quantifier binder is bound *outside* both states, so it must be visible in
        // the pre-state scope too: `Old(a[k])` under `forall k` reads the pre-state
        // array at the same `k` the postcondition is talking about.
        var pre = scope.Pre is null ? null : new SpecScope(scope.Pre);
        var inner = new SpecScope(scope) { Pre = pre };
        var binders = new List<string>();
        foreach (var b in q.Binders)
        {
            var name = Names.Local(b.Name);
            // Quantifier binders range over the mathematical values a spec talks about
            // (R4.6), so `forall (int i)` is `forall (var_i: int)`.
            var rendered = b.Type is IrPrim { IsMachineInt: true } ? "int" : Types.Render(b.Type);
            binders.Add($"({name}: {rendered})");
            var term = new Term(name, TermKind.Math, b.Type);
            inner.Bind(b.Name, term);
            pre?.Bind(b.Name, term);
        }

        var keyword = q.IsForall ? "forall" : "exists";
        var body = AsProp(Emit(q.Body, inner));
        return new Term(
            $"({keyword} {string.Join(" ", binders)}.{Pattern(q, inner)} {body})",
            TermKind.Prop);
    }

    /// <summary>
    /// R6.7b. The SMT trigger of a quantifier, chosen from its body the way a reader would
    /// choose it: the uninterpreted applications — element reads, sequence indexing and
    /// <c>[Spec]</c> calls — whose arguments are bound variables or other such terms.
    ///
    /// <para>F* encodes a <c>prop</c>-valued definition's body as a native SMT quantifier
    /// (FStarLang/FStar#4519), so a <c>[Spec]</c> function such as <c>Sorted</c> reaches the
    /// solver as a <c>forall</c> with no pattern, and Z3 is free to pick one that fires on
    /// every integer in the context. Inside a loop over an array that is enough to time
    /// out a goal as small as <c>j - 1 + 1 &lt;&lt; j + 1</c>. Naming the pattern
    /// instantiates the quantifier only at the reads the proof actually makes.</para>
    ///
    /// <para>Every term that covers all binders on its own is offered as an alternative;
    /// failing that, one multi-pattern is assembled greedily. A quantifier with no
    /// covering set of terms is left to the solver, as before.</para>
    /// </summary>
    private string Pattern(IrQuantifier q, SpecScope inner)
    {
        var bound = new HashSet<string>(q.Binders.Select(b => b.Name));
        // The body has already been emitted, with its diagnostics; a candidate is emitted
        // a second time only to learn its text, and must not report anything twice. One
        // that would not emit cleanly is not a trigger.
        var probeBag = new DiagnosticBag();
        var probe = new SpecEmitter(probeBag) { Bases = Bases };
        var candidates = new List<(string Text, HashSet<string> Covers)>();
        var seen = new HashSet<string>();
        Collect(q.Body, inner);

        if (candidates.Count == 0) return "";

        var singles = candidates.Where(c => c.Covers.SetEquals(bound)).Select(c => c.Text).ToList();
        if (singles.Count > 0)
            return "{:pattern " + string.Join(" \\/ ", singles) + "}";

        var chosen = new List<string>();
        var covered = new HashSet<string>();
        foreach (var c in candidates.OrderByDescending(c => c.Covers.Count))
        {
            if (c.Covers.IsSubsetOf(covered)) continue;
            chosen.Add(c.Text);
            covered.UnionWith(c.Covers);
            if (covered.SetEquals(bound)) break;
        }
        return covered.SetEquals(bound) ? "{:pattern " + string.Join("; ", chosen) + "}" : "";

        void Collect(IrExpr? e, SpecScope s)
        {
            switch (e)
            {
                case null:
                    return;
                case IrElement or IrSeqOp { Op: SeqOpKind.Index } or IrCall { Kind: CalleeKind.Spec }
                    when Mentions(e) is { Count: > 0 } covers && Triggerable(e, s):
                {
                    // Emitted in the scope it occurs in, so the pattern is textually the
                    // term the body contains — `Old(a[k])` is the pre-state read.
                    var errors = probeBag.Items.Length;
                    var text = probe.Emit(e, s).Text;
                    if (probeBag.Items.Length == errors && seen.Add(text))
                        candidates.Add((text, covers));
                    break;
                }
                case IrOld o when s.Pre is { } pre:
                    Collect(o.Operand, pre);
                    return;
                // A nested quantifier's terms may mention its own binders; they are its
                // triggers, not this one's.
                case IrQuantifier:
                    return;
            }
            foreach (var child in Children(e)) Collect(child, s);
        }

        HashSet<string> Mentions(IrExpr e)
        {
            var found = new HashSet<string>();
            Visit(e);
            return found;

            void Visit(IrExpr? x)
            {
                if (x is IrVar v && bound.Contains(v.Name)) found.Add(v.Name);
                if (x is IrQuantifier) return;
                foreach (var c in Children(x)) Visit(c);
            }
        }
    }

    /// <summary>
    /// Whether a term may appear in an SMT pattern: no interpreted symbol (arithmetic, a
    /// comparison, a connective, a conditional) anywhere in it, and no conversion that
    /// emits one (R13.2's truncation is a <c>%</c>).
    /// </summary>
    private static bool Triggerable(IrExpr e, SpecScope scope) => e switch
    {
        IrVar => true,
        IrLiteral { Value: not bool } => true,
        IrOld o => scope.Pre is not null && Triggerable(o.Operand, scope),
        IrContents c => Triggerable(c.Array, scope),
        IrLength l => Triggerable(l.Array, scope),
        IrElement el => Triggerable(el.Array, scope) && Triggerable(el.Index, scope),
        IrSeqOp { Op: SeqOpKind.Index or SeqOpKind.Length or SeqOpKind.SetAt } s
            => s.Args.All(a => Triggerable(a, scope)),
        IrCall { Kind: CalleeKind.Spec } call => call.Args.All(a => Triggerable(a, scope)),
        IrConvert { Operand.Type: IrPrim { Kind: var src }, Target: IrPrim { Kind: var dst } } cv
            => (src == dst || Types.RangeFits(src, dst)) && Triggerable(cv.Operand, scope),
        _ => false,
    };

    private static IEnumerable<IrExpr> Children(IrExpr? e) => e switch
    {
        IrUnary u => [u.Operand],
        IrBinary b => [b.Left, b.Right],
        IrConditional c => [c.Cond, c.Then, c.Else],
        IrElement el => [el.Array, el.Index],
        IrLength l => [l.Array],
        IrContents ct => [ct.Array],
        IrField f => [f.Receiver],
        IrObserve o => [o.Receiver],
        IrConvert cv => [cv.Operand],
        IrOld o => [o.Operand],
        IrQuantifier q => [q.Body],
        IrCall call => call.Args,
        IrSeqOp s => s.Args,
        IrListOp l => l.Args,
        IrSpecOp o => o.Args,
        _ => [],
    };

    /// <summary>
    /// A spec-position argument: mathematical for integers, the sequence for arrays
    /// (R4.6). This is what makes <c>Sorted(a, 0, a.Length)</c> translate.
    /// </summary>
    /// <summary>
    /// R3.5. A struct field holds a machine value, so a literal keeps its width suffix
    /// rather than becoming the mathematical integer a specification otherwise uses.
    /// </summary>
    /// <summary>
    /// Parenthesises a projection's receiver unless it is already atomic. Without this
    /// `!var_s.M.fld` would parse as `!(var_s.M.fld)` — a deref of a projection out of a
    /// reference — which is not what the C# `s.fld` on a `ref` parameter means.
    /// </summary>
    private static string Receiver(string text) =>
        text.Length > 0 && (char.IsLetter(text[0]) || text[0] is '_' or '(')
            ? text
            : $"({text})";

    /// <summary>
    /// R3.5. A field initialiser is read at the field's <em>declared</em> type, not at the
    /// initialiser's own: assigning an <c>int</c> field to a <c>SpecInt</c> one is C#'s
    /// implicit conversion, and in Pulse it is the `I32.v` that §6 puts on every machine
    /// integer entering the mathematical world.
    /// </summary>
    private string FieldValue(IrExpr expr, IrType? fieldType, SpecScope scope) => expr switch
    {
        IrLiteral l when fieldType is IrPrim { IsSpecNumeric: false } => Types.Literal(l.Value, expr.Type),
        IrLiteral l when fieldType is null => Types.Literal(l.Value, expr.Type),
        _ when fieldType is IrPrim { IsSpecNumeric: true } => AsMath(Emit(expr, scope)),
        _ => Emit(expr, scope).Text,
    };

    /// <summary>
    /// R4.13. A machine argument crosses into the mathematical world exactly when the
    /// parameter it is passed to lives there. A <c>[Spec]</c> function or <c>[Lemma]</c>
    /// may equally declare an <c>int</c> parameter — C# performs no conversion then, and
    /// neither does the translation.
    ///
    /// <para>R10.2b/R10.2c, in specification position. There is nothing to do. A class
    /// reference and a nullable reference to the same class are the <em>same</em> Pulse
    /// type — R10.2 makes <c>class_C</c> the refinement <c>b: class_C__opt { not (B.is_null
    /// b) }</c> — so C#'s implicit conversion is F*'s subtyping, and the null-forgiving
    /// <c>e!</c> the other way is a refinement check the solver discharges from the same
    /// branch condition C#'s own flow analysis used. Neither direction was ever visible in
    /// the IR, and now neither needs to be.</para>
    /// </summary>
    internal string Argument(IrExpr arg, IrType? paramType, SpecScope scope)
    {
        var term = Emit(arg, scope);
        return term.Kind == TermKind.Machine && paramType is not IrPrim { IsMachineInt: true }
            ? AsMath(term)
            : term.Text;
    }

    /// <summary>
    /// The type the *emitted* binder for parameter <paramref name="index"/> carries, or
    /// null when that binder is mathematical. R4.6 makes every parameter of a
    /// <c>[Spec]</c> function mathematical whatever its C# type; R4.7 leaves a
    /// <c>[Lemma]</c>'s binders with the types they were declared with, so only there
    /// does the C# parameter type decide.
    /// </summary>
    internal static IrType? ParamType(IrCall call, int index) =>
        call.Kind is CalleeKind.Spec ? null
        : index < call.ParamTypes.Length ? call.ParamTypes[index]
        : null;

    private Term TypeBoundMeasure(IrTypeBoundMeasure m, SpecScope scope)
    {
        if (!scope.TryGet(m.Counter, out var counter))
            return new Term("0", TermKind.Math);

        var kind = (counter.Type as IrPrim)?.Kind ?? PrimKind.Int;
        var bound = $"pow2 {Types.Width(kind) - (Types.IsSigned(kind) ? 1 : 0)}";
        return new Term(
            m.Increasing ? $"({bound} - {AsMath(counter)})" : $"({AsMath(counter)} + {bound})",
            TermKind.Math);
    }

    /// <summary>Renders a list of pure conjuncts as one <c>pure (...)</c> clause.</summary>
    public static string Conjunction(IEnumerable<string> conjuncts)
    {
        var list = conjuncts.Where(c => c.Length > 0).ToImmutableArray();
        return list.Length == 0 ? "True" : string.Join(" /\\\n           ", list);
    }
}
