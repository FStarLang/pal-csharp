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
    /// <summary>
    /// R4.9c and R4.12b. Whether an object parameter's invariant moves into the callee.
    /// Both halves of the rule are here rather than at the two places that need them,
    /// because the caller and the callee have to agree: the callee stops owing the
    /// invariant back, and the caller stops owning it, and a rule read differently at the
    /// two ends is a resource that is owned twice or not at all.
    /// </summary>
    public static bool Consumed(IrMethod method, IrParam p) =>
        p.Type is IrClassType &&
        (p.Consumes || (method.IsConstructor && p.Name != Names.This));

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
        // R4.11c. `IsReadOnly` is the *only* answer about the receiver. `Normalize.Mutated`
        // re-derives one from the body, and where the two disagreed the body's silently
        // won — so a `[Frac]` method that writes a field got a mutating signature here and
        // a read-only one everywhere else, and no one was told. Which of them is *right* is
        // a separation-logic question and F* answers it: a body emitted read-only cannot
        // write at a fraction, and Pulse says so against the method the user wrote.
        if (method.IsReadOnly) mutatedObjects.Remove(Names.This);

        var binders = ImmutableArray.CreateBuilder<string>();
        var ghostBinders = ImmutableArray.CreateBuilder<string>();

        // R14.2. Type parameters bind first, ahead of every value parameter, because a
        // value parameter's type may mention them. They are explicit rather than `#`
        // binders: R14.5 applies the type argument Roslyn already resolved at each call,
        // so no F* inference is relied on.
        foreach (var tp in method.TypeParameters)
            binders.Add($"({Names.TypeParam(tp)}: Type0)");
        // R14.2a. A type parameter the body takes `default` at needs its default supplied.
        foreach (var tp in method.DefaultedTypeParameters)
            binders.Add($"{{| _: Pulse.Lib.CSharp.Inhabited.has_default {Names.TypeParam(tp)} |}}");
        var preResources = ImmutableArray.CreateBuilder<string>();
        var postResources = ImmutableArray.CreateBuilder<string>();
        var postExistentials = ImmutableArray.CreateBuilder<string>();
        var prologue = ImmutableArray.CreateBuilder<(string Cell, string Source)>();

        var pre = new SpecScope();

        // R4.12/R9.15. A method that returns an object returns a *reference*, and a
        // reference is not something a specification can say anything about: what the
        // caller reasons with is the model the postcondition owns it at. So `Result`
        // denotes that model, not the binder — the same substitution R4.10 makes for
        // `this`, and the reason `Result.TheArea` means anything at all.
        var returnsObject = method.ReturnType is IrClassType { Plain: false };
        // R22.28. A method returning an array returns it owned, and `Result` denotes the
        // contents it is owned at, as an array parameter's name does (R4.9).
        var returnsArray = method.ReturnType is IrArrayType;
        var resultModel = "post_" + (method.IsConstructor ? Names.This : Names.Result);

        // Otherwise `Result` denotes the value the method returns, so it carries that
        // value's kind. Defaulting it to `Machine` is right for the common case and wrong
        // for a `bool`, which is already a proposition and must not be coerced with
        // `Int32.v`.
        var post = new SpecScope
        {
            Pre = pre,
            ResultTerm = returnsObject || returnsArray ? resultModel : Names.Result,
            ResultKind = returnsObject ? TermKind.Math : KindOf(method.ReturnType),
            ResultType = returnsObject ? null : method.ReturnType,
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
                    binders.Add($"({name}: array {Types.Atom(array.Element)})");
                    ghostBinders.Add($"(#{preValue}: erased (Seq.seq {Types.Atom(array.Element)}))");

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

                // R17.1/R17.6. A span parameter, which is the array case with one word
                // changed: `S.slice` for `array`, `S.pts_to` for `A.pts_to`. Everything
                // else — the contents binder, the `[Frac]` treatment, what `Pal.Contents`
                // denotes — is identical, because a span *is* its contents to a
                // specification just as an array is.
                //
                // A span parameter carries no receipt. The caller borrowed it and the
                // caller gives it back; a callee that took one is in the same position as
                // a callee that took an array, and R17.5's `Pal.Restore` is refused on it.
                case IrSpanType span:
                {
                    var preValue = "pre_" + p.Name;
                    var postValue = "post_" + p.Name;
                    binders.Add($"({name}: S.slice {Types.Atom(span.Element)})");
                    ghostBinders.Add($"(#{preValue}: erased (Seq.seq {Types.Atom(span.Element)}))");

                    var perm = p.Fraction is null ? "" : $"#{p.Fraction} ";
                    if (p.Fraction is not null) ghostBinders.Add($"(#{p.Fraction}: perm)");

                    preResources.Add($"S.pts_to {name} {perm}{preValue}");
                    if (p.Fraction is null)
                    {
                        postResources.Add($"S.pts_to {name} {postValue}");
                        postExistentials.Add(postValue);
                        post.Bind(p.Name, new Term(postValue, TermKind.Seq, p.Type));
                    }
                    else
                    {
                        postResources.Add($"S.pts_to {name} {perm}{preValue}");
                        post.Bind(p.Name, new Term($"(reveal {preValue})", TermKind.Seq, p.Type));
                    }

                    pre.Bind(p.Name, new Term($"(reveal {preValue})", TermKind.Seq, p.Type));
                    slots[p.Name] = new Slot(p.Name, p.Type, SlotKind.Span, name)
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
                    // R12.1. A `[Plain]` reference is passed and nothing is owned through
                    // it. There is no invariant to name, no model binder to quantify, and
                    // nothing to say in the postcondition: what this method owns is
                    // exactly what its `[Requires]` says, in the user's own predicate.
                    if (p.Plain)
                    {
                        binders.Add($"({name}: {Types.Render(p.Type)})");
                        // An ordinary immutable binder: the reference is a value like any
                        // other. What is *owned* through it is not the slot's business,
                        // because with `[Plain]` it never was the compiler's.
                        slots[p.Name] = new Slot(p.Name, p.Type, SlotKind.Value, name);
                        pre.Bind(p.Name, new Term(name, TermKind.Other, p.Type));
                        post.Bind(p.Name, new Term(name, TermKind.Other, p.Type));
                        break;
                    }

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
                    // R15.3. The receiver's model type is the class's model applied to
                    // the arguments the receiver's *type* carries; for a method of
                    // `Node<T>` they are the method's own type binders (R15.1).
                    var modelType = Types.Applied(
                        $"{Names.ClassModule(view)}.{Names.ClassModel(view)}",
                        (p.Type as IrClassType)?.TypeArguments ?? []);
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

                    // R10.3. A *nullable* reference is owned through the recursive
                    // `__inv_opt`, whose permission is positional (F36c). One local
                    // function keeps that difference out of every line below.
                    string Owned(string model) =>
                        klass.Nullable
                            ? $"{Names.ClassModule(klass.Name)}.{Names.ClassInvOpt(klass.Name)} " +
                              $"{name} {(fraction ?? "1.0R")} {model}"
                            : $"{inv} {name} {perm}{model}";

                    // An observed object contributes no existential: its permission is
                    // precisely the right to read, so the model cannot move and the one
                    // binder stands for the pre- and the post-state.
                    var observed = fraction is not null;

                    preResources.Add(Owned(preModel));

                    // R4.11. A method that changes no field cannot change the model, so
                    // the *same* binder stands for the pre- and the post-state. That is
                    // literally `preserves`: without it the caller would hold
                    // `exists* m'. inv this m'` and would have to be told, conjunct by
                    // conjunct, that nothing moved.
                    // R4.9c. `[Consumes]` transfers ownership to the callee, so the
                    // postcondition owns nothing: the object has moved into whatever the
                    // method built out of it. Without this a method such as an in-place
                    // append — which splices its argument into its result — would have to
                    // hand back an invariant it no longer has, and R10.7 would have to
                    // preserve a null case it must instead give up.
                    var moves = mutatedObjects.Contains(p.Name) && !observed;
                    // R4.12b. A constructor stores the objects it is given into the
                    // representation it is building, so ownership moves whether or not the
                    // author said `[Consumes]`: a body that may only assign fields (R4.12)
                    // has nowhere else to put one. Keeping the invariant in the
                    // postcondition would ask the caller to own the same object twice.
                    var consumed = Consumed(method, p);
                    if (consumed)
                    {
                        post.Bind(p.Name, new Term($"(reveal {preModel})", TermKind.Math, seen));
                    }
                    else if (moves)
                    {
                        postResources.Add(Owned(postModel));
                        postExistentials.Add(postModel);
                        post.Bind(p.Name, new Term(postModel, TermKind.Math, seen));
                    }
                    else
                    {
                        postResources.Add(Owned(preModel));
                        post.Bind(p.Name, new Term($"(reveal {preModel})", TermKind.Math, seen));
                    }

                    pre.Bind(p.Name, new Term($"(reveal {preModel})", TermKind.Math, seen));
                    slots[p.Name] = new Slot(p.Name, p.Type, SlotKind.Object, name)
                    {
                        Fraction = fraction,
                        PreModel = preModel,
                        PostModel = moves ? postModel : preModel,
                        ViewBase = view == klass.Name ? null : view,
                        Consumed = consumed,
                    };
                    break;
                }

                case var _ when p.Mode is ParamMode.Ref or ParamMode.Out or ParamMode.In:
                {
                    var preValue = "pre_" + p.Name;
                    var postValue = "post_" + p.Name;
                    binders.Add($"({name}: R.ref {Types.Atom(p.Type)})");
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
                    // R4.2: a by-value parameter is rebound as a cell only if assigned. A
                    // context parameter (R20.12) is a readonly field, never assigned, though
                    // passing it on to a callee looks like a write to Normalize.Assigned.
                    var isCell = assigned.Contains(p.Name) && !p.IsContext;
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
        //
        // R9.15 makes this every method's rule, not the constructor's: once a reference
        // conversion can happen at a `return`, an ordinary method can hand back an object
        // too, and the only difference is the name its contract calls it by.
        // R19.3. What an exception leaves the caller owning: every parameter, as the
        // postcondition owns it — and nothing the method was to return, since it returns
        // nothing. Snapshotted before the result's conjunct joins.
        var raisesResources = postResources.ToImmutable();
        var raisesExistentials = postExistentials.ToImmutable();

        if (method.ReturnType is IrClassType { Plain: false } built)
        {
            // R10.2. A method may return `C?`, and then what it owns is the nullable
            // invariant at full permission — the same conjunct R10.3a derives the non-null
            // one from. Nothing else about returning an object changes.
            postResources.Add(
                PulseEmitter.SubInvApp(built, Names.Result, "1.0R", resultModel));
            postExistentials.Add(resultModel);
            if (method.IsConstructor) post.Bind(Names.This, new Term(resultModel, TermKind.Math, built));
        }
        else if (returnsArray)
        {
            postResources.Add($"A.pts_to {Names.Result} {resultModel}");
            postExistentials.Add(resultModel);
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
        SlotOrder = [.. method.Parameters.Select(p => p.Name).Where(slots.ContainsKey)];

        // R12.2. A contract clause whose type is `SlProp` is an *ownership* clause, so it
        // joins the resources rather than the `pure`. This is the whole of what §12 adds to
        // the contract language: a user's predicate is applied like any other spec function
        // (R11.2), and where its application lands is decided by its C# type.
        //
        // Nothing else changes. A clause is a resource or it is a proposition, the two are
        // already assembled separately by `Clause`, and `**` between resources is what
        // `SlProp.operator *` means on the C# side.
        static bool IsResource(IrExpr e) => e.Type is IrPrim { Kind: PrimKind.SlProp };

        preResources.AddRange(method.Requires.Where(IsResource)
            .Select(r => _spec.Emit(r, pre).Text));
        postResources.AddRange(method.Ensures.Where(IsResource)
            .Select(e => _spec.Emit(e, post).Text));
        postResources.AddRange(method.Preserves.Where(IsResource)
            .Select(e => _spec.Emit(e, post).Text));
        preResources.AddRange(method.Preserves.Where(IsResource)
            .Select(e => _spec.Emit(e, pre).Text));

        var preConjuncts = method.Requires.Where(r => !IsResource(r))
            .Select(r => _spec.AsProp(_spec.Emit(r, pre))).ToImmutableArray();
        var postConjuncts = method.Ensures.Where(e => !IsResource(e))
            .Select(e => _spec.AsProp(_spec.Emit(e, post)))
            .Concat(method.Preserves.Where(e => !IsResource(e))
                .Select(e => _spec.AsProp(_spec.Emit(e, post))))
            .ToImmutableArray();

        _throws = method.Throws;
        if (!method.Throws.IsEmpty)
        {
            // R19.3. `[Throws]` predicates speak of the pre-state, so they mean the same
            // in the method's `raises` and in the `raises` of a `try` inside it.
            Raises = $"(fun ({Thrown}: exn) ->\n           " + Clause(raisesResources,
                UnderPrecondition(preConjuncts, [ThrowsProp(Thrown)]), raisesExistentials) + ")";
        }

        Requires = Clause(preResources.ToImmutable(), preConjuncts, []);
        Ensures = Clause(postResources.ToImmutable(), UnderPrecondition(preConjuncts, postConjuncts),
            postExistentials.ToImmutable());

        _ = diagnostics;
    }


    public ImmutableArray<string> Binders { get; }
    /// <summary>By-value parameters that must be rebound as cells (R4.2).</summary>
    public ImmutableArray<(string Cell, string Source)> Prologue { get; }
    public string Requires { get; }

    /// <summary>R19.3. The <c>raises</c> clause; null for a method that throws nothing.</summary>
    public string? Raises { get; }

    /// <summary>The binder of a <c>raises</c> clause.</summary>
    public const string Thrown = "thrown";

    private readonly ImmutableArray<IrThrows> _throws;

    /// <summary>
    /// R19.3. That the exception <paramref name="exn"/> is one the method declares: the
    /// disjunction, over its <c>[Throws]</c>, of the class's discriminator and the
    /// predicate, which may read the exception's fields as <c>Thrown</c>. A method that
    /// declares nothing may throw nothing, and Pulse makes it prove so.
    /// </summary>
    public string ThrowsProp(string exn)
    {
        if (_throws.IsEmpty) return "False";
        var scope = new SpecScope(PreScope);
        var cases = _throws.Select(t =>
        {
            scope.Bind(Frontend.FrontendPass.ThrownParameter, new Term(exn, TermKind.Other, t.Type));
            var parts = new List<string>();
            if (t.Type.Name is { } n) parts.Add($"{Names.Qualified(Names.ExnIs(n))} {exn}");
            if (t.When is { } w) parts.Add(_spec.AsProp(_spec.Emit(w, scope)));
            return parts.Count == 0 ? "True" : "(" + string.Join(" /\\ ", parts) + ")";
        });
        return string.Join(" \\/ ", cases);
    }
    public string Ensures { get; }
    public SpecScope PreScope { get; }
    public SpecScope PostScope { get; }
    public ImmutableDictionary<string, Slot> Slots { get; }

    /// <summary>
    /// The keys of <see cref="Slots"/> in the order the parameters were declared.
    /// <see cref="ImmutableDictionary{K,V}"/> enumerates in hash order, and .NET randomizes
    /// string hashing per process, so enumerating it directly makes the emitted order --
    /// and therefore the emitted text -- differ between runs of the same input. That
    /// defeats write-if-changed (R2.4) and re-verifies unchanged modules at random.
    /// </summary>
    public ImmutableArray<string> SlotOrder { get; }

    public static TermKind KindOf(IrType type) => type switch
    {
        IrPrim { IsMachineInt: true } => TermKind.Machine,
        IrPrim { Kind: PrimKind.Bool } => TermKind.Prop,
        IrPrim { IsSpecNumeric: true } => TermKind.Math,
        IrSeqType => TermKind.Seq,
        IrArrayType => TermKind.Seq,
        // R17.1. A span, like an array, *is* its contents wherever a specification
        // names it; only the resource holding those contents differs.
        IrSpanType => TermKind.Seq,
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
