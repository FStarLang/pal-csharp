using System.Collections.Immutable;
using System.Text;
using Pal.Compiler.Diagnostics;
using Pal.Compiler.Ir;
using Pal.Compiler.Passes;

namespace Pal.Compiler.Emit;

/// <summary>
/// The signature half of R4.1: how a method's parameters become Pulse binders, what
/// resources its contract owns, and what its specifications' free names denote in the
/// pre- and post-state.
/// </summary>
public sealed class MethodPlan
{
    private readonly SpecEmitter _spec;

    public MethodPlan(IrMethod method, SpecEmitter spec, DiagnosticBag diagnostics)
    {
        _spec = spec;

        var assigned = new HashSet<string>();
        Passes.Normalize.Assigned(method.Body, assigned);

        // R4.11 decides `preserves` from the body: `this` is mutated exactly when the
        // frontend found a field assignment, and any other object is mutated when the
        // body assigns through it or hands it somewhere that might.
        //
        // This is deliberately *not* `Normalize.Assigned`, which answers a different
        // question — which names need a mutable cell (R4.2) — and answers it by assuming
        // every argument of every call is written. That assumption is free for an `int`
        // and ruinous for an object: it re-quantifies the object's model in the
        // postcondition, so a caller learns nothing about the shape it just passed, and
        // `Result == a.TheArea` becomes a statement about a model no one can name.
        var mutatedObjects = new HashSet<string>();
        if (method.DeclaringClass is not null && !method.IsReadOnly) mutatedObjects.Add(Names.This);
        Normalize.Mutated(method.Body, mutatedObjects);

        var binders = ImmutableArray.CreateBuilder<string>();
        var ghostBinders = ImmutableArray.CreateBuilder<string>();
        var preResources = ImmutableArray.CreateBuilder<string>();
        var postResources = ImmutableArray.CreateBuilder<string>();
        var postExistentials = ImmutableArray.CreateBuilder<string>();
        var prologue = ImmutableArray.CreateBuilder<(string Cell, string Source)>();

        var pre = new SpecScope();
        // `Result` denotes the value the method returns, so it carries that value's kind.
        // Defaulting it to `Machine` is right for the common case and wrong for a `bool`,
        // which is already a proposition and must not be coerced with `Int32.v`.
        var post = new SpecScope
        {
            Pre = pre,
            ResultTerm = Names.Result,
            ResultKind = KindOf(method.ReturnType),
        };
        var slots = ImmutableDictionary.CreateBuilder<string, Slot>();

        foreach (var p in method.Parameters)
        {
            var name = Names.Local(p.Name);

            if (p.IsGhost)
            {
                ghostBinders.Add($"(#{name}: erased ({Types.Render(p.Type)}))");
                var term = new Term($"(reveal {name})", KindOf(p.Type), p.Type);
                pre.Bind(p.Name, term);
                post.Bind(p.Name, term);
                slots[p.Name] = new Slot(p.Name, p.Type, SlotKind.Value, name);
                continue;
            }

            switch (p.Type)
            {
                case IrArrayType array:
                {
                    var preValue = "pre_" + p.Name;
                    var postValue = "post_" + p.Name;
                    binders.Add($"({name}: array {Types.Render(array.Element)})");
                    ghostBinders.Add($"(#{preValue}: erased (Seq.seq {Types.Render(array.Element)}))");

                    // R4.9. `[Frac("p")]` introduces a permission variable and makes the
                    // parameter read-only: the contents cannot change, so the same binder
                    // stands for the pre- and the post-state and no existential is needed.
                    // The caller keeps the rest of the permission and so may share the
                    // array with a second parameter.
                    var perm = p.Fraction is null ? "" : $"#{p.Fraction} ";
                    if (p.Fraction is not null) ghostBinders.Add($"(#{p.Fraction}: perm)");

                    preResources.Add($"A.pts_to {name} {perm}{preValue}");
                    if (p.Fraction is null)
                    {
                        postResources.Add($"A.pts_to {name} {postValue}");
                        postExistentials.Add(postValue);
                        post.Bind(p.Name, new Term(postValue, TermKind.Seq, p.Type));
                    }
                    else
                    {
                        postResources.Add($"A.pts_to {name} {perm}{preValue}");
                        post.Bind(p.Name, new Term($"(reveal {preValue})", TermKind.Seq, p.Type));
                    }

                    pre.Bind(p.Name, new Term($"(reveal {preValue})", TermKind.Seq, p.Type));
                    slots[p.Name] = new Slot(p.Name, p.Type, SlotKind.Array, name)
                    {
                        Fraction = p.Fraction,
                    };
                    break;
                }

                // R4.10. An object parameter is owned through its invariant, not through a
                // `pts_to`: the ghost binder is the *model*, so a caller reasons about the
                // object only through the abstraction, and the representation stays
                // hidden. Structurally it is the `ref` case with `class_C__inv` in place
                // of `R.pts_to`, which is why the two read alike.
                case IrClassType klass:
                {
                    var preModel = "pre_" + p.Name;
                    var postModel = "post_" + p.Name;

                    // R9.7/R9.14. An `override`'s receiver is owned through
                    // `class_C__as_B`, not through `class_C__inv`: the vtable slot it fills
                    // is typed at *B*'s model, so the contract it inherited talks about B's
                    // model and the body must still see C's fields. `as_B` is exactly that
                    // — C's own invariant, indexed by B's model. Both predicates have the
                    // same shape `inv x #p m`, which is why one substitution suffices and
                    // no other rule below changes.
                    var view = p.Name == Names.This && method.Overrides is { } b ? b : klass.Name;
                    var modelType = $"{Names.ClassModule(view)}.{Names.ClassModel(view)}";
                    var inv = view == klass.Name
                        ? $"{Names.ClassModule(klass.Name)}.{Names.ClassInv(klass.Name)}"
                        : $"{Names.ClassModule(klass.Name)}.{Names.ClassAsBase(klass.Name, view)}";
                    var seen = view == klass.Name ? p.Type : new IrClassType(view);

                    binders.Add($"({name}: {Types.Render(p.Type)})");
                    ghostBinders.Add($"(#{preModel}: erased ({modelType}))");

                    // R4.9a: `[Frac("p")]` weakens an object parameter to an observation.
                    // R4.11b: a *receiver* the write-set analysis has already found
                    // read-only gets the same weakening with no annotation, because there
                    // it is a pure generalisation (F26) — a caller with full ownership is
                    // unaffected, Pulse instantiates the binder at `1.0R` — and because
                    // R3.10c propagates the fraction into sub-object invariants, so
                    // without it no fractional owner could read its own parts.
                    var fraction = p.Fraction;
                    if (fraction is null && p.Name == Names.This && !mutatedObjects.Contains(p.Name))
                        fraction = Names.Permission(p.Name);
                    if (fraction is not null) ghostBinders.Add($"(#{fraction}: perm)");
                    var perm = fraction is null ? "" : $"#{fraction} ";

                    // An observed object contributes no existential: its permission is
                    // precisely the right to read, so the model cannot move and the one
                    // binder stands for the pre- and the post-state.
                    var observed = fraction is not null;

                    preResources.Add($"{inv} {name} {perm}{preModel}");

                    // R4.11. A method that changes no field cannot change the model, so
                    // the *same* binder stands for the pre- and the post-state. That is
                    // literally `preserves`: without it the caller would hold
                    // `exists* m'. inv this m'` and would have to be told, conjunct by
                    // conjunct, that nothing moved.
                    var moves = mutatedObjects.Contains(p.Name) && !observed;
                    if (moves)
                    {
                        postResources.Add($"{inv} {name} {postModel}");
                        postExistentials.Add(postModel);
                        post.Bind(p.Name, new Term(postModel, TermKind.Math, seen));
                    }
                    else
                    {
                        postResources.Add($"{inv} {name} {perm}{preModel}");
                        post.Bind(p.Name, new Term($"(reveal {preModel})", TermKind.Math, seen));
                    }

                    pre.Bind(p.Name, new Term($"(reveal {preModel})", TermKind.Math, seen));
                    slots[p.Name] = new Slot(p.Name, p.Type, SlotKind.Object, name)
                    {
                        Fraction = fraction,
                        PreModel = preModel,
                        PostModel = moves ? postModel : preModel,
                        ViewBase = view == klass.Name ? null : view,
                    };
                    break;
                }

                case var _ when p.Mode is ParamMode.Ref or ParamMode.Out or ParamMode.In:
                {
                    var preValue = "pre_" + p.Name;
                    var postValue = "post_" + p.Name;
                    binders.Add($"({name}: R.ref {Types.Render(p.Type)})");
                    ghostBinders.Add($"(#{preValue}: erased ({Types.Render(p.Type)}))");

                    var refPerm = p.Fraction is null ? "" : $"#{p.Fraction} ";
                    if (p.Fraction is not null) ghostBinders.Add($"(#{p.Fraction}: perm)");

                    preResources.Add($"R.pts_to {name} {refPerm}{preValue}");
                    if (p.Fraction is null)
                    {
                        postResources.Add($"R.pts_to {name} {postValue}");
                        postExistentials.Add(postValue);
                        post.Bind(p.Name, new Term(postValue, KindOf(p.Type), p.Type));
                    }
                    else
                    {
                        postResources.Add($"R.pts_to {name} {refPerm}{preValue}");
                        post.Bind(p.Name, new Term($"(reveal {preValue})", KindOf(p.Type), p.Type));
                    }

                    pre.Bind(p.Name, new Term($"(reveal {preValue})", KindOf(p.Type), p.Type));
                    slots[p.Name] = new Slot(p.Name, p.Type, SlotKind.RefParam, name)
                    {
                        Fraction = p.Fraction,
                    };
                    break;
                }

                default:
                {
                    // R4.2: a by-value parameter is rebound as a cell only if assigned.
                    var isCell = assigned.Contains(p.Name);
                    var binder = isCell ? Names.Argument(p.Name) : name;
                    binders.Add($"({binder}: {Types.Render(p.Type)})");
                    if (isCell) prologue.Add((name, binder));
                    var term = new Term(binder, KindOf(p.Type), p.Type);
                    pre.Bind(p.Name, term);
                    post.Bind(p.Name, term);
                    slots[p.Name] = new Slot(p.Name, p.Type,
                        isCell ? SlotKind.Cell : SlotKind.Value, isCell ? name : binder);
                    break;
                }
            }
        }

        // R4.12. A constructor takes no object and returns one: there is no invariant to
        // require, and the postcondition owns the object it has just built. `this` in the
        // contract names that object, so a constructor's `[Ensures]` reads exactly like
        // any other method's. Freshness comes free from the frame rule (F15): the caller's
        // other objects are in the frame, so the new one cannot be any of them.
        if (method is { IsConstructor: true, ReturnType: IrClassType built })
        {
            var postModel = "post_" + Names.This;
            postResources.Add(
                $"{Names.ClassModule(built.Name)}.{Names.ClassInv(built.Name)} {Names.Result} {postModel}");
            postExistentials.Add(postModel);
            post.Bind(Names.This, new Term(postModel, TermKind.Math, built));
        }

        // F12: a Pulse `fn` must have at least one binder, so a parameterless C# method
        // takes the unit argument its Pulse counterpart is called with.
        Binders = binders.Count == 0 && ghostBinders.Count == 0
            ? ["()"]
            : [.. binders, .. ghostBinders];
        Prologue = prologue.ToImmutable();
        PreScope = pre;
        PostScope = post;
        Slots = slots.ToImmutable();

        var preConjuncts = method.Requires.Select(r => _spec.AsProp(_spec.Emit(r, pre))).ToImmutableArray();
        var postConjuncts = method.Ensures.Select(e => _spec.AsProp(_spec.Emit(e, post)))
            .Concat(method.Preserves.Select(e => _spec.AsProp(_spec.Emit(e, post))))
            .ToImmutableArray();

        Requires = Clause(preResources.ToImmutable(), preConjuncts, []);
        Ensures = Clause(postResources.ToImmutable(), UnderPrecondition(preConjuncts, postConjuncts),
            postExistentials.ToImmutable());

        _ = diagnostics;
    }


    public ImmutableArray<string> Binders { get; }
    /// <summary>By-value parameters that must be rebound as cells (R4.2).</summary>
    public ImmutableArray<(string Cell, string Source)> Prologue { get; }
    public string Requires { get; }
    public string Ensures { get; }
    public SpecScope PreScope { get; }
    public SpecScope PostScope { get; }
    public ImmutableDictionary<string, Slot> Slots { get; }

    public static TermKind KindOf(IrType type) => type switch
    {
        IrPrim { IsMachineInt: true } => TermKind.Machine,
        IrPrim { Kind: PrimKind.Bool } => TermKind.Prop,
        IrPrim { IsSpecNumeric: true } => TermKind.Math,
        IrSeqType => TermKind.Seq,
        IrArrayType => TermKind.Seq,
        _ => TermKind.Other,
    };

    /// <summary>
    /// R4.8. A Pulse <c>ensures</c> is type-checked in a context that does *not*
    /// include the <c>requires</c>, so a postcondition whose well-typedness depends
    /// on the precondition — <c>Result == s[i]</c> guarded by <c>i &lt; s.Length</c>
    /// is the everyday case — is rejected before any proof is attempted. Restating
    /// the precondition as a hypothesis fixes that without weakening anything: the
    /// precondition is expressed entirely over the pre-state binders, which are
    /// still in scope in the postcondition, and the caller has just discharged it,
    /// so <c>PRE ==&gt; POST</c> gives the caller exactly <c>POST</c>.
    /// </summary>
    public static ImmutableArray<string> UnderPrecondition(
        ImmutableArray<string> pre, ImmutableArray<string> post)
    {
        var hypotheses = pre.Where(p => p.Length > 0).ToImmutableArray();
        var goals = post.Where(p => p.Length > 0).ToImmutableArray();
        if (hypotheses.Length == 0 || goals.Length == 0) return post;
        return [$"({SpecEmitter.Conjunction(hypotheses)}) ==> ({SpecEmitter.Conjunction(goals)})"];
    }

    /// <summary>Assembles a <c>requires</c>/<c>ensures</c>/<c>invariant</c> clause.</summary>
    public static string Clause(
        ImmutableArray<string> resources,
        ImmutableArray<string> pureConjuncts,
        ImmutableArray<string> existentials)
    {
        var parts = resources.Where(r => r.Length > 0).ToList();
        var pure = pureConjuncts.Where(p => p.Length > 0).ToList();
        if (pure.Count > 0)
            parts.Add($"pure ({SpecEmitter.Conjunction(pure)})");
        if (parts.Count == 0) parts.Add("emp");

        var body = string.Join(" **\n           ", parts);
        return existentials.Length == 0
            ? body
            : $"exists* {string.Join(" ", existentials)}.\n           {body}";
    }
}
