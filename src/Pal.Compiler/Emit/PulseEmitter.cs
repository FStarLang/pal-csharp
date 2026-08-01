using System.Collections.Immutable;
using System.Text;
using Pal.Compiler.Diagnostics;
using Pal.Compiler.Ir;

namespace Pal.Compiler.Emit;

/// <summary>
/// R2.2. The C# a generated top-level construct came from. <c>Construct</c> is the
/// emitted F* name, or <c>"*"</c> for a module whose whole text is the user's own Pulse.
/// </summary>
public sealed record Provenance(string Construct, IrLoc Loc);

/// <summary>A generated Pulse module.</summary>
public sealed record EmittedModule(string Name, string Text)
{
    public string FileName => Name + ".fst";

    /// <summary>
    /// R2.2. What this module declares and where each declaration came from. A construct
    /// absent from here was invented by the emitter, which the provenance lint reports:
    /// anything the translator produces that no C# asked for has to be justified as a
    /// numbered rule in doc/translation.md.
    /// </summary>
    public ImmutableArray<Provenance> Origin { get; init; } = ImmutableArray<Provenance>.Empty;
}

/// <summary>
/// How a C# name is represented in the emitted Pulse: as an immutable binder, as a
/// mutable <c>ref</c> cell, or as a live array with a ghost contents binder.
/// </summary>
public sealed record Slot(string Name, IrType Type, SlotKind Kind, string Binder)
{
    /// <summary>
    /// The permission variable introduced by <c>[Frac("p")]</c>, if any. A slot that has
    /// one is read-only: it can be observed but not written, here or by a callee.
    /// </summary>
    public string? Fraction { get; init; }

    private string Perm => Fraction is null ? "" : $"#{Fraction} ";

    /// <summary>The resource conjunct owning this slot, given a value binder.</summary>
    public string Resource(string value) => Kind switch
    {
        SlotKind.Cell => $"R.pts_to {Binder} {value}",
        SlotKind.RefParam => $"R.pts_to {Binder} {Perm}{value}",
        SlotKind.Array => $"A.pts_to {Binder} {Perm}{value}",
        _ => "",
    };

    public bool Owns => Kind is SlotKind.Cell or SlotKind.RefParam or SlotKind.Array;
}

public enum SlotKind
{
    /// <summary>An immutable by-value parameter; no resource.</summary>
    Value,
    /// <summary>A local, or a by-value parameter the body assigns (R5.2, R4.2).</summary>
    Cell,
    /// <summary>A <c>ref</c>/<c>out</c>/<c>in</c> parameter.</summary>
    RefParam,
    /// <summary>An array parameter.</summary>
    Array,
}

/// <summary>
/// The Emit stage: one Pulse module per C# declaration, following
/// <c>doc/translation.md</c>. The emitter contributes no proof steps of its own
/// (§0 rule 3); everything it writes is either the user's code, the user's
/// annotations, or a call into <c>Pulse.Lib.CSharp.*</c>.
/// </summary>
public sealed class PulseEmitter(DiagnosticBag diagnostics)
{
    private readonly SpecEmitter _spec = new(diagnostics);

    public ImmutableArray<EmittedModule> Emit(IrProgram program)
    {
        var modules = ImmutableArray.CreateBuilder<EmittedModule>();
        foreach (var decl in program.Declarations)
        {
            var module = decl switch
            {
                IrSpecFunction s => EmitSpecFunction(s),
                IrMethod { IsLemma: true } m => EmitLemma(m),
                IrMethod m => EmitMethod(m),
                IrStruct s => EmitStruct(s),
                IrIncludePulse i => new EmittedModule(i.Module, i.Text),
                _ => null,
            };
            if (module is null) continue;

            var construct = decl switch
            {
                IrSpecFunction s => Names.SpecFunction(s.Name),
                IrMethod { IsLemma: true } m => Names.Lemma(m.Name),
                IrMethod m => Names.Function(m.Name),
                IrStruct s => Names.StructType(s.Name),
                _ => "*",
            };

            // R3.4 emits three constructs for one C# declaration — the record, its
            // refinement predicate, and the refined type — so all three are recorded
            // against the same span rather than leaving two of them unaccounted for.
            ImmutableArray<Provenance> origin = decl is IrStruct st
                ?
                [
                    new Provenance(Names.StructRaw(st.Name), decl.Loc),
                    new Provenance(Names.StructPred(st.Name), decl.Loc),
                    new Provenance(Names.StructType(st.Name), decl.Loc),
                ]
                : [new Provenance(construct, decl.Loc)];

            modules.Add(module with { Origin = origin });
        }
        return modules.ToImmutable();
    }

    // =======================================================================
    // [Spec] functions (R4.6)
    // =======================================================================

    private EmittedModule EmitSpecFunction(IrSpecFunction fn)
    {
        var scope = new SpecScope();
        var binders = new List<string>();

        foreach (var p in fn.Parameters)
        {
            var name = Names.Local(p.Name);
            switch (p.Type)
            {
                case IrArrayType a:
                    binders.Add($"({name}: Seq.seq {Types.Render(a.Element)})");
                    scope.Bind(p.Name, new Term(name, TermKind.Seq, p.Type));
                    break;
                case IrPrim { IsMachineInt: true }:
                    // R4.6: a [Spec] method's integer parameters are mathematical.
                    binders.Add($"({name}: int)");
                    scope.Bind(p.Name, new Term(name, TermKind.Math, p.Type));
                    break;
                default:
                    binders.Add($"({name}: {Types.Render(p.Type)})");
                    scope.Bind(p.Name, new Term(name, TermKind.Other, p.Type));
                    break;
            }
        }

        // R4.6: the [Requires] clauses refine the last binder, so that the body
        // type-checks under them.
        if (fn.Requires.Length > 0 && binders.Count > 0)
        {
            var refinement = SpecEmitter.Conjunction(fn.Requires.Select(r => _spec.AsProp(_spec.Emit(r, scope))));
            var last = binders[^1];
            binders[^1] = last[..^1] + " { " + refinement + " })";
        }

        var body = _spec.Emit(fn.Body, scope);
        var returnType = fn.ReturnType is IrPrim { Kind: PrimKind.Bool } ? "prop" : Types.Render(fn.ReturnType);
        var text = fn.ReturnType is IrPrim { Kind: PrimKind.Bool } ? _spec.AsProp(body) : body.Text;

        var sb = new StringBuilder();
        sb.AppendLine($"module {Names.SpecModule(fn.Name)}");
        sb.AppendLine();
        foreach (var open in Dependencies(
                     Names.SpecModule(fn.Name), null, fn.Requires, [fn.Body]))
            sb.AppendLine($"open {open}");
        sb.AppendLine(Preamble.Modules);
        sb.AppendLine();
        sb.Append(fn.IsRecursive ? "let rec " : "let ").Append(Names.SpecFunction(fn.Name));
        foreach (var b in binders) sb.Append(' ').Append(b);
        sb.AppendLine();
        // A measure belongs to the effect annotation, so a recursive definition is
        // written `: Tot t (decreases m)` rather than `: t`.
        sb.AppendLine(fn.IsRecursive && fn.Decreases is not null
            ? $"  : Tot {returnType} (decreases {_spec.Math(fn.Decreases, scope)})"
            : $"  : {returnType}");
        sb.AppendLine($"  = {text}");

        return new EmittedModule(Names.SpecModule(fn.Name), sb.ToString());
    }

    // =======================================================================
    // [Lemma] declarations (R4.7)
    // =======================================================================

    /// <summary>
    /// A <c>[Lemma]</c> is a proof step about the values the program actually holds at
    /// the point it is applied, so — unlike a <c>[Spec]</c> function (R4.6) — its
    /// parameters keep the program's types: <c>int</c> is <c>I32.t</c>, and an array is
    /// its contents sequence. It becomes an ordinary F* <c>Lemma</c>, which is exactly
    /// what Pulse admits as a ghost statement.
    /// </summary>
    private EmittedModule EmitLemma(IrMethod lemma)
    {
        var scope = new SpecScope { ResultTerm = Names.Result };
        var binders = new List<string>();

        foreach (var p in lemma.Parameters)
        {
            var name = Names.Local(p.Name);
            var (rendered, kind) = p.Type switch
            {
                IrArrayType a => ($"Seq.seq {Types.Render(a.Element)}", TermKind.Seq),
                IrSeqType s => ($"Seq.seq {Types.Render(s.Element)}", TermKind.Seq),
                IrGhostType g => (Types.Render(g.Inner), MethodPlan.KindOf(g.Inner)),
                _ => (Types.Render(p.Type), MethodPlan.KindOf(p.Type)),
            };
            binders.Add($"({name}: {rendered})");
            scope.Bind(p.Name, new Term(name, kind, p.Type));
        }

        var requires = SpecEmitter.Conjunction(lemma.Requires.Select(r => _spec.AsProp(_spec.Emit(r, scope))));
        var ensures = SpecEmitter.Conjunction(
            lemma.Ensures.Concat(lemma.Preserves).Select(e => _spec.AsProp(_spec.Emit(e, scope))));

        var sb = new StringBuilder();
        sb.AppendLine($"module {Names.SpecModule(lemma.Name)}");
        sb.AppendLine();
        foreach (var open in Dependencies(
                     Names.SpecModule(lemma.Name), null, lemma.Requires, lemma.Ensures, lemma.Preserves))
            sb.AppendLine($"open {open}");
        sb.AppendLine(Preamble.Modules);
        sb.AppendLine();
        sb.Append("let ").Append(Names.Lemma(lemma.Name));
        foreach (var b in binders) sb.Append(' ').Append(b);
        sb.AppendLine();
        sb.AppendLine($"  : Lemma (requires ({requires}))");
        sb.AppendLine($"          (ensures ({ensures}))");

        var body = lemma switch
        {
            { Admit: true } => "admit()",
            { PulseBody: { } raw } => Antiquotation.Expand(raw, scope),
            _ => "()",
        };
        sb.AppendLine($"  = {body}");

        return new EmittedModule(Names.SpecModule(lemma.Name), sb.ToString());
    }

    // =======================================================================
    // Structs (R3.4)
    // =======================================================================

    /// <summary>
    /// A C# <c>struct</c> is a value — it has no identity, assignment copies it, and
    /// nothing can hold a pointer into the middle of one — so it needs an F* record and
    /// nothing else. Where PAL emits a spec type, fold/unfold predicates and per-field
    /// pointer projectors, all of that machinery exists to model C's interior pointers,
    /// which C# does not have.
    /// </summary>
    private EmittedModule EmitStruct(IrStruct s)
    {
        var scope = new SpecScope();
        foreach (var f in s.Fields)
            // Inside the defining module the field name needs no qualifier — and must
            // not have one, or F*'s dependency scan reads the module as depending on
            // itself.
            scope.Bind(f.Name, new Term(
                $"this.{Names.Field(f.Name)}", MethodPlan.KindOf(f.Type), f.Type));

        var predicate = s.Refinements.Length == 0
            ? "True"
            : SpecEmitter.Conjunction(s.Refinements.Select(r => _spec.AsProp(_spec.Emit(r, scope))));

        var sb = new StringBuilder();
        sb.AppendLine($"module {Names.StructModule(s.Name)}");
        sb.AppendLine();
        sb.AppendLine(Preamble.Modules);
        sb.AppendLine();
        sb.Append("noeq type ").Append(Names.StructRaw(s.Name)).AppendLine(" = {");
        foreach (var f in s.Fields)
            sb.AppendLine($"  {Names.Field(f.Name)}: {Types.Render(f.Type)};");
        sb.AppendLine("}");
        sb.AppendLine();
        // The refinement predicate is emitted even when trivial: uniform output beats
        // output whose shape depends on whether the user happened to write [Refine].
        sb.AppendLine($"let {Names.StructPred(s.Name)} (this: {Names.StructRaw(s.Name)}) : prop =");
        sb.AppendLine($"  {predicate}");
        sb.AppendLine();
        sb.AppendLine($"type {Names.StructType(s.Name)} = " +
                      $"this: {Names.StructRaw(s.Name)} {{ {Names.StructPred(s.Name)} this }}");

        return new EmittedModule(Names.StructModule(s.Name), sb.ToString());
    }

    // =======================================================================
    // Methods (R4.1)
    // =======================================================================

    private EmittedModule EmitMethod(IrMethod method)
    {
        var body = new CodeEmitter(_spec, diagnostics);
        var plan = new MethodPlan(method, _spec, diagnostics);

        var sb = new StringBuilder();
        sb.AppendLine($"module {Names.FunctionModule(method.Name)}");
        sb.AppendLine("#lang-pulse");
        sb.AppendLine();
        foreach (var open in Dependencies(
                     Names.FunctionModule(method.Name), method.Body,
                     method.Requires, method.Ensures, method.Preserves))
            sb.AppendLine($"open {open}");
        sb.AppendLine(Preamble.Opens);
        sb.AppendLine();
        sb.AppendLine(Preamble.Modules);
        sb.AppendLine();

        sb.Append("fn ").Append(Names.Function(method.Name));
        foreach (var b in plan.Binders) sb.Append(' ').Append(b);
        sb.AppendLine();
        sb.AppendLine($"  requires {plan.Requires}");
        if (method.ReturnType is not IrPrim { Kind: PrimKind.Void })
            sb.AppendLine($"  returns  {Names.Result}: {Types.Render(method.ReturnType)}");
        sb.AppendLine($"  ensures  {plan.Ensures}");
        sb.AppendLine("{");

        if (method.Admit)
        {
            sb.AppendLine("  admit()");
        }
        else if (method.PulseBody is { } raw)
        {
            foreach (var line in Antiquotation.Expand(raw, plan.PreScope).Split('\n'))
                sb.AppendLine("  " + line.TrimEnd());
        }
        else if (method.Body is not null)
        {
            sb.Append(body.EmitBody(method, plan));
        }

        sb.AppendLine("}");

        return new EmittedModule(Names.FunctionModule(method.Name), sb.ToString());
    }

    /// <summary>
    /// Modules this declaration's translation must <c>open</c>: one per <c>[Spec]</c>
    /// function, <c>[Lemma]</c> or method it mentions, anywhere — including inside a
    /// loop invariant, which is easy to forget and produces an "identifier not found"
    /// only once F* runs.
    /// </summary>
    private static ImmutableArray<string> Dependencies(
        string self, IrStmt? body, params IEnumerable<IrExpr>[] specifications)
    {
        var names = new HashSet<string>();
        Collect(body);
        foreach (var group in specifications)
            foreach (var e in group) CollectExpr(e);

        void Collect(IrStmt? s)
        {
            switch (s)
            {
                case null: return;
                case IrBlock b: foreach (var x in b.Statements) Collect(x); return;
                case IrLocalDecl d: CollectExpr(d.Init); return;
                case IrAssign a: CollectExpr(a.Target); CollectExpr(a.Value); return;
                case IrIf i: CollectExpr(i.Cond); Collect(i.Then); Collect(i.Else); return;
                case IrWhile w:
                    CollectExpr(w.Cond);
                    foreach (var inv in w.Invariants) CollectExpr(inv);
                    Collect(w.Body);
                    return;
                case IrReturn r: CollectExpr(r.Value); return;
                case IrExprStmt e: CollectExpr(e.Expr); return;
                case IrGhostStmt g: CollectExpr(g.Prop); return;
                default: return;
            }
        }

        void CollectExpr(IrExpr? e)
        {
            switch (e)
            {
                case null: return;
                case IrCall c:
                    names.Add(c.Kind is CalleeKind.Spec or CalleeKind.Lemma
                        ? Names.SpecModule(c.Callee)
                        : Names.FunctionModule(c.Callee));
                    foreach (var a in c.Args) CollectExpr(a);
                    return;
                case IrBinary b: CollectExpr(b.Left); CollectExpr(b.Right); return;
                case IrUnary u: CollectExpr(u.Operand); return;
                case IrConditional t: CollectExpr(t.Cond); CollectExpr(t.Then); CollectExpr(t.Else); return;
                case IrElement el: CollectExpr(el.Array); CollectExpr(el.Index); return;
                case IrLength l: CollectExpr(l.Array); return;
                case IrOld o: CollectExpr(o.Operand); return;
                case IrContents ct: CollectExpr(ct.Array); return;
                case IrSeqOp s: foreach (var a in s.Args) CollectExpr(a); return;
                case IrQuantifier q: CollectExpr(q.Body); return;
                case IrConvert cv: CollectExpr(cv.Operand); return;
                default: return;
            }
        }

        names.Remove(self);
        return [.. names.OrderBy(n => n, StringComparer.Ordinal)];
    }

}

/// <summary>The fixed header every generated module carries.</summary>
public static class Preamble
{
    public const string Opens =
        """
        open Pulse
        open Pulse.Lib.CSharp.Array
        open Pulse.Lib.CSharp.Casts
        """;

    public const string Modules =
        """
        module R = Pulse.Lib.Reference
        module A = Pulse.Lib.Array
        module I8 = FStar.Int8
        module I16 = FStar.Int16
        module I32 = FStar.Int32
        module I64 = FStar.Int64
        module U8 = FStar.UInt8
        module U16 = FStar.UInt16
        module U32 = FStar.UInt32
        module U64 = FStar.UInt64
        module Seq = FStar.Seq
        module CS = Pulse.Lib.CSharp.Seq
        """;
}
