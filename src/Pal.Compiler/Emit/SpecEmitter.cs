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

    public SpecScope() { }

    public SpecScope(SpecScope other)
    {
        _values = new Dictionary<string, Term>(other._values);
        Pre = other.Pre;
        ResultTerm = other.ResultTerm;
        DefiningClass = other.DefiningClass;
        ResultKind = other.ResultKind;
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
                return l.Value is bool b
                    ? new Term(b ? "True" : "False", TermKind.Prop)
                    : new Term(Render(l.Value), TermKind.Math);

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
                return new Term(result, scope.ResultKind, r.Type);

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
                    TermKind.Machine, el.Type);
            }

            case IrSeqOp s:
                return SeqOp(s, scope);

            case IrListOp l:
                return ListOp(l, scope);

            case IrSpecOp o:
                return SpecOp(o, scope);

            // R10.2. `null` is `None`. The type annotation is what lets F* infer the
            // option's parameter in `pure (x == None)` positions where nothing else
            // determines it.
            case IrNull n:
                return new Term(
                    n.Type is IrClassType nullClass
                        ? $"(None #{Names.ClassModule(nullClass.Name)}.{Names.ClassType(nullClass.Name)})"
                        : "None",
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
                return new Term(
                    $"({Names.SpecFunction(call.Callee)} " +
                    string.Join(" ", call.Args.Select(a => Argument(a, scope))) + ")",
                    call.ResultType is IrPrim { IsMachineInt: true } ? TermKind.Math : TermKind.Prop,
                    call.ResultType);

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
        SeqOpKind.Rotate => new Term(
            $"(CS.rotate {Emit(s.Args[0], scope).Text} {Math(s.Args[1], scope)})",
            TermKind.Seq),
        SeqOpKind.IsPermutation => new Term(
            $"(CS.is_permutation {Emit(s.Args[0], scope).Text} {Emit(s.Args[1], scope).Text})",
            TermKind.Prop),
        _ => new Term("True", TermKind.Prop),
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
        _ => new Term("True", TermKind.Prop),
    };

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
        var text = op.Args.IsEmpty
            ? op.Function
            : $"({op.Function} {string.Join(" ", op.Args.Select(a => AsMath(Emit(a, scope))))})";
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
        return new Term(
            $"({keyword} {string.Join(" ", binders)}. {AsProp(Emit(q.Body, inner))})",
            TermKind.Prop);
    }

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
