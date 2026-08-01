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

    public SpecScope() { }

    public SpecScope(SpecScope other)
    {
        _values = new Dictionary<string, Term>(other._values);
        Pre = other.Pre;
        ResultTerm = other.ResultTerm;
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
    public Term Emit(IrExpr expr, SpecScope scope)
    {
        switch (expr)
        {
            case IrLiteral l:
                return l.Value is bool b
                    ? new Term(b ? "True" : "False", TermKind.Prop)
                    : new Term(Render(l.Value), TermKind.Math);

            case IrVar v when scope.TryGet(v.Name, out var bound):
                return bound;

            case IrVar v:
                diagnostics.Error("PALCS0300", v.Loc,
                    $"`{v.Name}` cannot be mentioned in this specification.");
                return new Term("()", TermKind.Other);

            case IrOld o when scope.Pre is { } pre:
                return Emit(o.Operand, pre);

            case IrOld o:
                diagnostics.Error("PALCS0301", o.Loc,
                    "`Pal.Old` is only meaningful in a postcondition or a loop invariant.");
                return new Term("()", TermKind.Other);

            case IrResult r when scope.ResultTerm is { } result:
                return new Term(result, TermKind.Machine, r.Type);

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
                return new Term($"(Seq.length {Emit(len.Array, scope).Text})", TermKind.Math);

            case IrElement el:
                return new Term(
                    $"(Seq.index {Emit(el.Array, scope).Text} {Math(el.Index, scope)})",
                    TermKind.Machine, el.Type);

            case IrSeqOp s:
                return SeqOp(s, scope);

            case IrQuantifier q:
                return Quantifier(q, scope);

            case IrCall { Kind: CalleeKind.Spec } call:
                return new Term(
                    $"({Names.SpecFunction(call.Callee)} " +
                    string.Join(" ", call.Args.Select(a => Argument(a, scope))) + ")",
                    TermKind.Prop);

            case IrConvert cv:
                // A widening conversion is the identity on mathematical values.
                return Emit(cv.Operand, scope) with { Type = cv.Target };

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
        _ => new Term($"({Emit(u.Operand, scope).Text})", TermKind.Other),
    };

    private Term Binary(IrBinary b, SpecScope scope)
    {
        string Infix(string op, TermKind kind, bool mathematical = true)
        {
            var left = mathematical ? Math(b.Left, scope) : AsProp(Emit(b.Left, scope));
            var right = mathematical ? Math(b.Right, scope) : AsProp(Emit(b.Right, scope));
            _ = kind;
            return $"({left} {op} {right})";
        }

        return b.Op switch
        {
            BinOp.Add => new Term(Infix("+", TermKind.Math), TermKind.Math),
            BinOp.Sub => new Term(Infix("-", TermKind.Math), TermKind.Math),
            BinOp.Mul => new Term(Infix("*", TermKind.Math), TermKind.Math),
            BinOp.Div => new Term(Infix("/", TermKind.Math), TermKind.Math),
            BinOp.Rem => new Term(Infix("%", TermKind.Math), TermKind.Math),
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
            _ => new Term(Infix("+", TermKind.Math), TermKind.Math),
        };
    }

    /// <summary>
    /// Equality is the one operator whose translation depends on the operands' kind:
    /// two sequences compare as sequences, two integers as mathematical integers.
    /// </summary>
    private string Equality(IrBinary b, SpecScope scope, bool negated)
    {
        var left = Emit(b.Left, scope);
        var right = Emit(b.Right, scope);
        var comparable = left.Kind is TermKind.Seq or TermKind.Bool or TermKind.Prop or TermKind.Other;
        var text = comparable
            ? $"({left.Text} == {right.Text})"
            : $"({AsMath(left)} == {AsMath(right)})";
        return negated ? $"(~ {text})" : text;
    }

    private Term SeqOp(IrSeqOp s, SpecScope scope) => s.Op switch
    {
        SeqOpKind.Length => new Term($"(Seq.length {Emit(s.Args[0], scope).Text})", TermKind.Math),
        SeqOpKind.Index => new Term(
            $"(Seq.index {Emit(s.Args[0], scope).Text} {Math(s.Args[1], scope)})",
            TermKind.Machine, ElementType(s.Args[0])),
        SeqOpKind.SetAt => new Term(
            $"(Seq.upd {Emit(s.Args[0], scope).Text} {Math(s.Args[1], scope)} {Emit(s.Args[2], scope).Text})",
            TermKind.Seq),
        SeqOpKind.Slice => new Term(
            $"(Seq.slice {Emit(s.Args[0], scope).Text} {Math(s.Args[1], scope)} {Math(s.Args[2], scope)})",
            TermKind.Seq),
        SeqOpKind.IsPermutation => new Term(
            $"(CS.is_permutation {Emit(s.Args[0], scope).Text} {Emit(s.Args[1], scope).Text})",
            TermKind.Prop),
        _ => new Term("True", TermKind.Prop),
    };

    private static IrType? ElementType(IrExpr sequence) => sequence.Type switch
    {
        IrSeqType s => s.Element,
        IrArrayType a => a.Element,
        _ => null,
    };

    private Term Quantifier(IrQuantifier q, SpecScope scope)
    {
        var inner = new SpecScope(scope);
        var binders = new List<string>();
        foreach (var b in q.Binders)
        {
            var name = Names.Local(b.Name);
            // Quantifier binders range over the mathematical values a spec talks about
            // (R4.6), so `forall (int i)` is `forall (var_i: int)`.
            var rendered = b.Type is IrPrim { IsMachineInt: true } ? "int" : Types.Render(b.Type);
            binders.Add($"({name}: {rendered})");
            inner.Bind(b.Name, new Term(name, TermKind.Math, b.Type));
        }

        var keyword = q.IsForall ? "forall" : "exists";
        return new Term(
            $"({keyword} {string.Join(" ", binders)}. {AsProp(Emit(q.Body, inner))})",
            TermKind.Prop);
    }

    /// <summary>
    /// A spec-position argument: mathematical for integers, the sequence for arrays
    /// (R4.6). This is what makes <c>Sorted(a, 0, a.Length)</c> translate.
    /// </summary>
    private string Argument(IrExpr arg, SpecScope scope)
    {
        var term = Emit(arg, scope);
        return term.Kind == TermKind.Machine ? AsMath(term) : term.Text;
    }

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
