using Pal.Compiler.Passes;
using System.Collections.Immutable;
using System.Text;
using Pal.Compiler.Diagnostics;
using Pal.Compiler.Ir;

namespace Pal.Compiler.Emit;

/// <summary>
/// Emits the executable half of a method (doc/translation.md §5, §6).
///
/// <para>
/// Two rules govern everything here. <b>A-normalisation (R6.2):</b> every stateful
/// subexpression — a read of a cell, an array subscript, a call — is let-bound to a
/// fresh temporary, in C#'s left-to-right evaluation order; pure operations stay inline.
/// <b>Structure preservation (§0 rule 2):</b> loops stay loops, both branches of an
/// <c>if</c> are always emitted, and no statement is reordered, merged or elided.
/// </para>
/// </summary>
public sealed class CodeEmitter(
    SpecEmitter spec,
    DiagnosticBag diagnostics,
    IReadOnlyDictionary<string, IrClass>? classes = null)
{
    /// <summary>
    /// The output, one line at a time, each remembering the C# it came from.
    ///
    /// A list of lines rather than a <c>StringBuilder</c> because <see cref="Capture"/>
    /// emits into this buffer, takes the text back out and re-appends it somewhere else,
    /// and doing that to a character buffer means splitting text back into lines to move
    /// it — which is exactly the operation that would silently misalign a position map.
    /// Lines that are never joined cannot come apart.
    /// </summary>
    private readonly List<EmittedLine> _lines = [];

    /// <summary>The C# a line is currently being emitted for; see <see cref="Statement"/>.</summary>
    private IrLoc? _loc;

    private readonly Dictionary<string, Slot> _slots = [];
    private int _indent = 1;
    private int _temp;
    private int _ghost;
    private int _loop;

    /// <summary>
    /// R5.10. The escape flags of the innermost loop being emitted, or null outside any
    /// loop. <c>Break</c> is allocated before the loop and read by its guard and measure;
    /// <c>Continue</c> is allocated inside the body and reset on every iteration.
    /// </summary>
    private sealed record Escape(string? Break, string? Continue);

    private Escape? _escape;

    /// <summary>
    /// R4.10. The objects this method holds, in declaration order. Each is unfolded once
    /// on entry and re-folded on every exit; between the two the body owns the
    /// representation and may read and write fields.
    /// </summary>
    private ImmutableArray<Slot> _objects = ImmutableArray<Slot>.Empty;

    /// <summary>
    /// R4.14. Objects allocated by this method. Their invariants are owned here and, unless
    /// the reference is returned, are still owned when the method ends — so they must be
    /// dropped. This is where the CLR's garbage collector enters the translation: F15 says
    /// Pulse slprops are affine, so the resource may simply be discarded, but Pulse still
    /// requires the discard to be *written*.
    /// </summary>
    private readonly List<Slot> _objectLocals = [];

    /// <summary>
    /// How many enclosing blocks would have to discard what they declared as they close
    /// (F19). Zero means the nearest enclosing block ends at the method's exit, where the
    /// postcondition is known.
    /// </summary>
    private int _closingBlocks;

    private string Fresh() => "t" + _temp++;
    private string FreshValue(string name) => $"v{name}_{_ghost++}";

    private void Line(string text) =>
        _lines.Add(new EmittedLine(new string(' ', _indent * 2) + text + "\n", _loc));

    private string Text() => string.Concat(_lines.Select(l => l.Text));

    /// <summary>
    /// What line of the emitted body each C# construct produced, for mapping an F* error
    /// back to the source. Line numbers are one-based and relative to the body, which is
    /// all this class knows; <c>PulseEmitter</c> shifts them by where the body was placed.
    /// </summary>
    public ImmutableArray<LineOrigin> Origins()
    {
        var origins = ImmutableArray.CreateBuilder<LineOrigin>();
        var line = 1;
        foreach (var emitted in _lines)
        {
            if (emitted.Loc is { } loc) origins.Add(new LineOrigin(line, loc));
            line += emitted.Text.Count(c => c == '\n');
        }
        return origins.ToImmutable();
    }

    public string EmitBody(IrMethod method, MethodPlan plan)
    {
        foreach (var (name, slot) in plan.Slots) _slots[name] = slot;

        if (method is { IsConstructor: true, ReturnType: IrClassType built })
        {
            // R4.2 applies here too, and the prologue has to precede the initialisers: a
            // constructor's parameter becomes a cell on the same conservative test as any
            // other method's, and until R3.10b nothing had ever handed one to a call, so
            // the omission was unreachable rather than absent.
            foreach (var (cell, source) in plan.Prologue) Line($"let mut {cell} = {source};");
            Construct(method, built);
            return Text();
        }

        // R4.10. Only the *receiver* of the class's own methods is opened. An object that
        // merely passes through — a parameter of a static method, or an argument on its
        // way to a callee — must stay folded, because every function that takes it expects
        // its invariant, not its representation. The receiver is the one object whose
        // fields this body may name at all (PALCS0523 refuses the rest), so the bracket
        // goes exactly where the field accesses are.
        _objects = method.DeclaringClass is not null &&
                   plan.Slots.TryGetValue(Names.This, out var self) &&
                   self.Kind == SlotKind.Object
            ? [self]
            : [];

        // The invariant is abstract to the caller, so the body cannot touch a field until
        // it is unfolded, and the matching `fold` on each exit path re-establishes it.
        foreach (var obj in _objects) OpenReceiver(obj);

        // R4.2: rebind assigned by-value parameters as cells.
        foreach (var (cell, source) in plan.Prologue) Line($"let mut {cell} = {source};");

        var statements = method.Body is IrBlock b ? b.Statements : [method.Body!];
        EmitSequence(statements, method, plan);
        return Text();
    }

    /// <summary>
    /// Emits a statement sequence in <em>tail</em> position: the last statement supplies
    /// the block's value (R5.5). Every earlier statement is emitted for its effect, and
    /// a <c>return</c> among them is an error — Normalize's R5.5b has already moved the
    /// ones it can into branches.
    /// </summary>
    private void EmitSequence(ImmutableArray<IrStmt> statements, IrMethod method, MethodPlan plan)
    {
        for (var i = 0; i < statements.Length - 1; i++)
        {
            if (statements[i] is IrReturn early)
            {
                diagnostics.Unsupported(early.Loc, "A `return` that is not the last statement",
                    "pal-csharp translates a method body as a single block, so a `return` " +
                    "must be reachable as the block's value.");
                return;
            }
            Statement(statements[i], plan);
        }

        if (statements.Length > 0) Tail(statements[^1], method, plan);
        else
        {
            if (NeedsEpilogue) CloseObjects(method, plan);
            if (IsVoid(method)) Line("()");
        }
    }

    private static bool IsVoid(IrMethod method) => method.ReturnType is IrPrim { Kind: PrimKind.Void };

    /// <summary>
    /// Emits the statement whose value is the enclosing block's value. Only three shapes
    /// can occupy that position; anything else is emitted for its effect and the block
    /// closes with <c>()</c>, which is well typed exactly when the method returns void.
    /// </summary>
    private void Tail(IrStmt stmt, IrMethod method, MethodPlan plan)
    {
        var outer = _loc;
        _loc = stmt.Loc;
        try { TailCore(stmt, method, plan); } finally { _loc = outer; }
    }

    private void TailCore(IrStmt stmt, IrMethod method, MethodPlan plan)
    {
        switch (stmt)
        {
            case IrReturn { Value: null }:
                if (NeedsEpilogue) CloseObjects(method, plan);
                Line("()");
                return;

            case IrReturn ret:
            {
                // The value is computed *before* the closing `fold`, because computing it
                // may read a field and so needs the representation still open; it is
                // let-bound so that the `fold` can be interposed between the read and the
                // block's value.
                var text = Expr(ret.Value!);
                if (!NeedsEpilogue) { Line(text); return; }

                // A returned object must keep the binder the callee produced it under:
                // re-binding it would leave the context holding its invariant under the
                // old name, which the frame rule cannot match (Error 228). Everything else
                // is let-bound so the epilogue can be interposed before the block's value.
                if (IsObjectBinder(text)) { CloseObjects(method, plan, text); Line(text); return; }

                var t = Fresh();
                Line($"let {t} = {text};");
                CloseObjects(method, plan);
                Line(t);
                return;
            }

            case IrBlock b:
                Scoped(() => EmitSequence(b.Statements, method, plan), dropAtEnd: false);
                return;

            case IrIf { Else: not null } i:
            {
                var cond = Expr(i.Cond);
                Line($"if ({cond}) {{");
                _indent++;
                Tail(i.Then, method, plan);
                _indent--;
                Line("} else {");
                _indent++;
                Tail(i.Else, method, plan);
                _indent--;
                Line("}");
                return;
            }

            default:
                Statement(stmt, plan);
                if (NeedsEpilogue) CloseObjects(method, plan);
                if (IsVoid(method)) Line("()");
                return;
        }
    }

    // =======================================================================
    // Objects (R4.10-R4.11a)
    // =======================================================================

    /// <summary>
    /// R4.12. A constructor allocates the representation, establishes the invariant on it
    /// and returns the object. Nothing is freed: Pulse slprops are affine and the CLR is
    /// garbage collected (F15).
    ///
    /// <para>The body is required to be a sequence of field initialisations, because that
    /// is what a record literal can express. A constructor that reads a field it has
    /// written, or calls a method on the half-built object, is refused rather than
    /// approximated: two-phase initialisation needs an invariant that holds of a partial
    /// object, which the scheme does not have.</para>
    /// </summary>
    private void Construct(IrMethod method, IrClassType built)
    {
        if (classes is null || !classes.TryGetValue(built.Name, out var decl))
        {
            diagnostics.Unsupported(method.Loc, $"A constructor of `{built.Name}`");
            return;
        }

        var initialisers = new Dictionary<string, string>();
        foreach (var stmt in method.Body is IrBlock b ? b.Statements : [method.Body!])
        {
            if (stmt is IrAssign { Target: IrField { Receiver: IrVar { Name: Names.This } } f } a)
            {
                initialisers[f.Field] = Expr(a.Value);
                continue;
            }
            if (stmt is IrBlock { Statements.IsEmpty: true }) continue;
            diagnostics.Unsupported(stmt.Loc, "A constructor statement that is not a field initialisation",
                "A constructor may only assign its own fields: the object's invariant does " +
                "not hold until every field has a value, so nothing else can run first.");
            return;
        }

        var fields = new List<string>();
        foreach (var (field, i) in decl.Fields.Select((f, i) => (f, i)))
        {
            if (!initialisers.TryGetValue(field.Name, out var value))
            {
                diagnostics.Unsupported(method.Loc,
                    $"A constructor that leaves `{field.Name}` uninitialised",
                    "Assign every field: the invariant is established over the whole " +
                    "representation, so a default-valued field would have to satisfy it by luck.");
                return;
            }
            fields.Add((i == 0 ? Names.ClassProjection(decl.Name, field.Name) : Names.Field(field.Name))
                       + " = " + value);
        }

        Line($"let {Names.Result} = B.alloc ({{ {string.Join("; ", fields)} }});");

        var slot = new Slot(Names.This, built, SlotKind.Object, Names.Result)
        {
            PreModel = null,
            PostModel = "post_" + Names.This,
        };
        Line($"fold {Inv(built)} {Names.Result} {ModelWitness(decl, slot)};");
        Line(Names.Result);
    }


    private bool IsObjectBinder(string text) =>
        _objectLocals.Any(l => l.Binder == text) || _objects.Any(o => o.Binder == text);

    private static string Inv(IrClassType c) =>
        $"{Names.ClassModule(c.Name)}.{Names.ClassInv(c.Name)}";

    /// <summary>
    /// R5.12. The receiver's resources <em>as R4.10 left them</em>: a <c>Box</c> holding the
    /// representation record, and one <c>A.pts_to</c> for every array the class owns.
    ///
    /// A loop in the unfolded window has to carry exactly these, because they are what its
    /// body touches. All of them are existential: R3.6 writes a whole record, so the record
    /// binder changes on any field write, and an element write changes an array's contents.
    /// The array *references* survive that, because a record update is definitionally equal
    /// to the original in every field it does not mention.
    ///
    /// Each field is bound in the invariant's scope under <c>this.f</c>, so a user writing
    /// <c>Pal.Invariant("i &lt;= top")</c> inside the method means the representation's
    /// <c>top</c> — the same reading R3.9b gives a class-level <c>[Invariant]</c>, and for
    /// the same reason. An array field denotes its contents (R3.10a).
    ///
    /// What is <em>not</em> carried is the class's own <c>[Invariant]</c> clauses. They may
    /// be transiently false — that is what the window is for — so the emitter states only
    /// what it owns: the resources, and the length bound that comes from C#'s array type
    /// rather than from anything the user wrote. Every other proposition the loop needs is
    /// the user's to state, which is R5.8's rule unchanged.
    /// </summary>
    private void Representation(
        Slot receiver,
        IrStmt body,
        SpecScope scope,
        SpecScope measureScope,
        ImmutableArray<string>.Builder resources,
        ImmutableArray<string>.Builder existentials,
        ImmutableArray<string>.Builder pure,
        List<(string Name, string Resource)> fixedNames)
    {
        var klass = (IrClassType)receiver.Type;
        var (writesRecord, written) = ReceiverWrites(body);

        var record = FreshValue("rep");
        var recordResource = $"B.pts_to {receiver.Binder} {receiver.PermArg}{record}";
        resources.Add(recordResource);
        if (writesRecord) existentials.Add(record);
        else fixedNames.Add((record, recordResource));

        // F3. A `decreases` measure may name a field only when the loop leaves it alone,
        // because then the record has a name from before the loop. A loop that writes a
        // field quantifies the record existentially, and F3 forbids a measure that mentions
        // the invariant's existentials — so the binding is simply absent, and naming the
        // field in a measure is refused where it is written.
        void BindBoth(string key, Term term, bool stable)
        {
            scope.Bind(key, term);
            if (stable) measureScope.Bind(key, term);
        }

        if (classes is null || !classes.TryGetValue(klass.Name, out var decl)) return;

        foreach (var f in decl.Fields)
        {
            var projection = $"{record}.{Names.ClassProjection(klass.Name, f.Name)}";
            if (f.Type is IrClassType)
            {
                // R3.10b. A sub-object is carried by its invariant, at its model, exactly
                // as an array is carried by its `A.pts_to` at its contents. Inside the
                // loop it is still *folded*, so the body may call its methods.
                var sub = FreshValue(Names.SubModel(f.Name));
                var subResource =
                    $"{PulseEmitter.SubInv(f.Type)} {projection} {receiver.PermArg}{sub}";
                resources.Add(subResource);
                var settled = !writesRecord && !written.Contains(f.Name);
                if (settled) fixedNames.Add((sub, subResource));
                else existentials.Add(sub);
                BindBoth($"{Names.This}.{f.Name}", new Term(sub, TermKind.Math, f.Type), settled);
                continue;
            }
            if (f.Type is IrArrayType)
            {
                var contents = FreshValue(Names.Contents(f.Name));
                var resource = $"A.pts_to {projection} {receiver.PermArg}{contents}";
                resources.Add(resource);
                var stable = !writesRecord && !written.Contains(f.Name);
                if (stable)
                {
                    fixedNames.Add((contents, resource));
                }
                else
                {
                    existentials.Add(contents);

                    // No C# operation changes the length of an array it has been handed, so
                    // a loop that only writes *elements* leaves the length where it was. The
                    // invariant has to say so all the same, because the contents are
                    // existentially quantified and an existential remembers nothing. Naming
                    // the length before the loop is what gives it something to be equal to.
                    // Like the bound below, this conjunct comes from C#'s array type rather
                    // than from anything the user wrote, which is why the emitter states it.
                    if (!writesRecord)
                    {
                        var entry = FreshValue(Names.Contents(f.Name));
                        fixedNames.Add((entry, resource.Replace(contents, entry)));
                        pure.Add($"Seq.length {contents} == Seq.length {entry}");
                    }
                }
                pure.Add($"Seq.length {contents} <= 2147483647");
                BindBoth($"{Names.This}.{f.Name}", new Term(contents, TermKind.Seq, f.Type), stable);
            }
            else
            {
                BindBoth($"{Names.This}.{f.Name}",
                    new Term(projection, MethodPlan.KindOf(f.Type), f.Type), !writesRecord);
            }
        }
    }

    /// <summary>
    /// What a loop body does to the receiver, which decides which halves of R5.12's
    /// representation have to be existentially quantified. A field assignment replaces the
    /// whole record (R3.6), so it unsettles everything; an element write unsettles only
    /// that array's contents; handing an owned array to a callee is treated as an element
    /// write, because the callee may write it.
    /// </summary>
    private (bool Record, HashSet<string> Arrays) ReceiverWrites(IrStmt body)
    {
        var arrays = new HashSet<string>(StringComparer.Ordinal);
        var record = false;

        foreach (var stmt in Check.Statements(body))
        {
            if (stmt is IrAssign a)
            {
                switch (a.Target)
                {
                    case IrField { Receiver: IrVar { Name: Names.This }, Field: var f }:
                        record = true;
                        arrays.Add(f);
                        break;
                    case IrElement { Array: IrField { Receiver: IrVar { Name: Names.This }, Field: var g } }:
                        arrays.Add(g);
                        break;
                }
            }

            foreach (var node in Check.Expressions(stmt).SelectMany(Check.Subexpressions))
            {
                if (node is not IrCall call) continue;
                for (var i = 0; i < call.Args.Length; i++)
                {
                    if (call.Args[i] is not IrField { Receiver: IrVar { Name: Names.This }, Field: var h })
                        continue;

                    // The one case a field survives being handed to a callee: it is the
                    // receiver of an instance method R4.11 has already found read-only, so
                    // the callee's own postcondition says its model did not move. Anything
                    // else — an array passed as data, a mutating method, a static callee —
                    // is assumed to write it, which is the strict direction and costs only
                    // an existential.
                    if (i == 0 && call.HasReceiver && !call.MutatesReceiver) continue;
                    arrays.Add(h);
                }
            }
        }

        return (record, arrays);
    }


    /// <summary>
    /// R9.15. The class an initialiser actually produces, when the frontend recorded one.
    /// A reference conversion is invisible in C# and has to be read off the two types.
    /// </summary>
    private static string? Source(IrExpr? init) => init switch
    {
        IrCall { ResultType: IrClassType c } => c.Name,
        _ => null,
    };

    /// <summary>
    /// R9.15. <c>B x = new D(...);</c>. The object is allocated at its own class, its
    /// invariant is read at the base's model through R9.14's view, and the upcast returns
    /// the reference the base-typed name is bound to.
    /// </summary>
    private void Upcast(IrLocalDecl d, IrExpr init, string derived, IrClassType target, string binder)
    {
        if (classes is null || !classes.TryGetValue(derived, out var sub) ||
            sub.BaseClass != target.Name)
        {
            diagnostics.Unsupported(d.Loc,
                $"Converting a `{derived}` to a `{target.Name}`",
                "R9.15 inserts an upcast only from a class to its immediate base; " +
                "a longer chain would need one upcast per level, which \u00a79 has not probed.");
            return;
        }

        var impl = Fresh();
        if (init is IrCall { Kind: CalleeKind.Method } call) Call(call, impl);
        else Line($"let {impl} = {Expr(init)};");

        // The view is folded at the forgetting of whatever model the constructor
        // established, which is the same expression R9.6 read off the `[Model]` override.
        var own = FreshValue(d.Name);
        var mod = Names.ClassModule(derived);
        Line($"with {own}. assert ({mod}.{Names.ClassInv(derived)} {impl} {own});");
        Line($"fold ({mod}.{Names.ClassAsBase(derived, target.Name)} {impl} " +
             $"({mod}.{Names.ClassForget(derived)} {own}));");
        Line($"let {binder} = {Names.VtblModule(derived)}." +
             $"{Names.UpcastTo(derived, target.Name)} {impl};");

        var local = new Slot(d.Name, target, SlotKind.Object, binder);
        _slots[d.Name] = local;
        _objectLocals.Add(local);
    }

    private static string Unfold(Slot obj) =>
        $"unfold {Inv((IrClassType)obj.Type)} {obj.Binder} {obj.PermArg}{obj.PreModel}";

    /// <summary>
    /// R4.10's fold/unfold bracket, opened. R9.14: an <c>override</c> is handed its
    /// receiver at the base's model, so there is one bracket more to open — the view
    /// first, then the class's own invariant inside it. The <c>with</c> is how the body
    /// gets a name for its own model, which the view existentially quantifies.
    /// </summary>
    private void OpenReceiver(Slot obj)
    {
        var klass = (IrClassType)obj.Type;
        if (obj.ViewBase is not { } b) { Line(Unfold(obj) + ";"); return; }

        Line($"unfold {Names.ClassModule(klass.Name)}." +
             $"{Names.ClassAsBase(klass.Name, b)} {obj.Binder} {obj.PermArg}{obj.PreModel};");
        Line($"with {obj.OwnModel}. assert ({Inv(klass)} {obj.Binder} {obj.PermArg}{obj.OwnModel});");
        Line($"unfold {Inv(klass)} {obj.Binder} {obj.PermArg}{obj.OwnModel};");
    }

    /// <summary>
    /// R4.11a — the fold witness. A read-only method re-folds at the binder it was handed:
    /// its model did not change, and re-folding at a *recomputed* model instead leaves
    /// Pulse two syntactically different indices to reconcile, which it will not do
    /// (Error 228). A mutator has no such binder to appeal to, so it re-folds at the
    /// abstraction function applied to the representation it has just written — the same
    /// expression the class module puts in the invariant, evaluated at the post-state.
    /// </summary>
    private bool NeedsEpilogue => _objects.Length > 0 || _objectLocals.Count > 0;

    /// <summary>
    /// R4.14. Discards the invariant of every object this method allocated and did not
    /// hand back. <c>with m. assert …</c> names the existential witness the context is
    /// holding, which <c>drop_</c> needs because it takes an slprop and not a name.
    /// </summary>
    /// <summary>
    /// R4.14's scope rule. An object local's resource is discarded where C# says its name
    /// goes out of scope — at the end of the block that declares it — and not merely at
    /// the end of the method. A block that is *not* in tail position drops what it
    /// declared as it closes; one that is leaves the discard to the return, which knows
    /// which object is being handed back.
    ///
    /// Either way the block's declarations leave the list on the way out. Without that,
    /// an object allocated in one arm of an `if` would be dropped in the other, where its
    /// binder does not exist.
    /// </summary>
    private void Scoped(Action emit, bool dropAtEnd)
    {
        var mark = _objectLocals.Count;
        if (dropAtEnd) _closingBlocks++;
        emit();
        if (dropAtEnd) { _closingBlocks--; DropLocals(null, mark); }
        _objectLocals.RemoveRange(mark, _objectLocals.Count - mark);
    }

    private void DropLocals(string? returned, int from = 0)
    {
        foreach (var local in _objectLocals.Skip(from))
        {
            if (local.Binder == returned) continue;
            var klass = (IrClassType)local.Type;
            var m = FreshValue(local.Name);
            Line($"with {m}. assert ({Inv(klass)} {local.Binder} {m});");
            Line($"drop_ ({Inv(klass)} {local.Binder} {m});");
        }
    }

    private void CloseObjects(IrMethod method, MethodPlan plan, string? returned = null)
    {
        DropLocals(returned);

        foreach (var obj in _objects)
        {
            var klass = (IrClassType)obj.Type;
            // R4.11a. A read-only method re-folds at the binder it was handed; under a
            // view (R9.14) that binder names the class's *own* model, which the opening
            // `with` introduced, and the view closes at the base model it was given.
            if (obj.PostModel == obj.PreModel)
            {
                var own = obj.ViewBase is null ? obj.PreModel : obj.OwnModel;
                Line($"fold {Inv(klass)} {obj.Binder} {obj.PermArg}{own};");
                CloseView(obj, obj.PreModel!);
                continue;
            }

            if (classes is null || !classes.TryGetValue(klass.Name, out var decl))
            {
                diagnostics.Unsupported(method.Loc,
                    $"Mutating an object of class `{klass.Name}` whose model is not in this translation unit");
                continue;
            }

            var witness = ModelWitness(decl, obj);
            if (obj.ViewBase is null)
            {
                Line($"fold {Inv(klass)} {obj.Binder} {witness};");
                continue;
            }

            // A mutator under a view re-folds twice, and the outer index is the inner one
            // pushed through R9.6's forgetting function. That is what makes an override
            // satisfy the base's postcondition: the base's model of the post-state *is*
            // the forgetting of this class's model of it.
            var post = Fresh();
            Line($"let {post} = {witness};");
            Line($"fold {Inv(klass)} {obj.Binder} {obj.PermArg}{post};");
            CloseView(obj, $"({Names.ClassModule(klass.Name)}.{Names.ClassForget(klass.Name)} {post})");
        }
    }

    /// <summary>R9.14. Closes the base-model view an <c>override</c>'s receiver is held at.</summary>
    private void CloseView(Slot obj, string model)
    {
        if (obj.ViewBase is not { } b) return;
        var klass = (IrClassType)obj.Type;
        Line($"fold {Names.ClassModule(klass.Name)}." +
             $"{Names.ClassAsBase(klass.Name, b)} {obj.Binder} {obj.PermArg}{model};");
    }

    /// <summary>
    /// The abstraction function applied to the object's current representation: the
    /// <c>[Model]</c> member's body, with each field read through the box.
    /// </summary>
    private string ModelWitness(IrClass decl, Slot obj)
    {
        var raw = Fresh();
        Line($"let {raw} = B.op_Bang {obj.Binder};");

        var scope = new SpecScope();
        foreach (var field in decl.Fields)
        {
            var projection = $"{raw}.{Names.ClassProjection(decl.Name, field.Name)}";
            if (field.Type is IrArrayType)
            {
                // R3.10a. The abstraction reads an array field's *contents*, and the
                // contents are an existential the context is holding rather than anything
                // this method named — the array has been written since the `unfold`, so
                // even the binder the `unfold` produced is stale. `with c. assert p`
                // names what is actually there, which is the same device R4.14 needs.
                var contents = FreshValue(field.Name);
                Line($"with {contents}. assert (A.pts_to {projection} {contents});");
                scope.Bind(field.Name, new Term(contents, TermKind.Seq, field.Type));
                continue;
            }
            if (field.Type is IrClassType)
            {
                // R3.10b, and the same device for the same reason. A sub-object's model
                // may have moved since the `unfold` — that is what calling a method on it
                // does — so the abstraction reads whatever model the context is now
                // holding for it, not the one the `unfold` produced.
                var subModel = FreshValue(Names.SubModel(field.Name));
                Line($"with {subModel}. assert " +
                     $"({PulseEmitter.SubInv(field.Type)} {projection} {subModel});");
                scope.Bind(field.Name, new Term(subModel, TermKind.Math, field.Type));
                continue;
            }
            scope.Bind(field.Name, new Term(
                projection, MethodPlan.KindOf(field.Type), field.Type));
        }

        // R9.2: only a class with a representation has an abstraction function, and only
        // such a class reaches here — an abstract class's model is supplied by its leaves.
        var body = decl.ModelBody ?? throw new InvalidOperationException(
            $"{decl.Name} has no abstraction function");
        return MethodPlan.KindOf(decl.ModelType) == TermKind.Math
            ? spec.Math(body, scope)
            : $"({spec.Emit(body, scope).Text})";
    }

    // =======================================================================
    // Statements
    // =======================================================================

    private void Statement(IrStmt stmt, MethodPlan plan)
    {
        // Every line emitted from here down belongs to this statement, unless a nested
        // statement claims it first. Saving and restoring rather than just assigning is
        // what keeps a block's closing lines attributed to the block and not to whatever
        // it happened to contain last.
        var outer = _loc;
        _loc = stmt.Loc;
        try { StatementCore(stmt, plan); } finally { _loc = outer; }
    }

    private void StatementCore(IrStmt stmt, MethodPlan plan)
    {
        switch (stmt)
        {
            // R3.8. An object local binds a reference. C# can rebind it, but nothing in
            // the supported subset does, and binding it immutably is what lets it be
            // handed to a callee that consumes and returns its invariant.
            case IrLocalDecl { Type: IrClassType, Init: IrVar alias } d
                when Lookup(alias.Name) is { Kind: SlotKind.Object } aliased:
            {
                // R3.8, the other half. `C x = y;` binds a second C# name to one object; it
                // allocates nothing and owns nothing, because the invariant is attached to
                // `y` and Pulse matches resources by name. So the translation is to *share
                // the slot*: `x` and `y` denote the same Pulse binder, and every rule that
                // consults a slot — R4.14's discard, R5.13's lemma, an argument position —
                // sees one object, which is what C# says there is.
                //
                // Emitting `let var_x = var_y;` instead would leave the context holding
                // `inv var_y _` while every later mention asked for `inv var_x _`, and no
                // pure equality closes that gap (Error 228).
                _slots[d.Name] = aliased with { Name = d.Name };
                return;
            }

            case IrLocalDecl { Type: IrClassType oc, Init: not null } d:
            {
                // F19. The discard would land at this block's close, where Pulse is still
                // solving for the block's postcondition and cannot open the object's
                // model existential. Refused rather than emitted (§0 rule 3).
                if (_closingBlocks > 0)
                {
                    diagnostics.Unsupported(d.Loc,
                        $"`new {oc.Name}()` in a nested block",
                        "An object allocated here would be discarded where the enclosing " +
                        "block closes (R4.14), and a block in statement position has no " +
                        "postcondition of its own for the discard to be checked against: " +
                        "Pulse reports `Cannot find witness` for the object's model (F19). " +
                        "Allocate it in the method's own block, or in a branch that " +
                        "returns.");
                    return;
                }

                var binder = Names.Local(d.Name);

                // R9.15. A C# reference conversion: the initialiser produces a subclass and
                // the name is declared at a base class. The conversion is what makes the
                // object's own invariant readable as the base's, so it is emitted here,
                // where C# performs it, and nowhere else.
                if (Source(d.Init) is { } derived && derived != oc.Name)
                {
                    Upcast(d, d.Init, derived, oc, binder);
                    return;
                }

                // The initialiser is emitted *into* the local's binder rather than into a
                // temporary the local then aliases. Pulse matches resources syntactically:
                // after `let var_c = t0` the context still holds `inv t0 _`, and no amount
                // of pure equality will let the frame rule find `inv var_c _` (Error 228).
                if (d.Init is IrCall { Kind: CalleeKind.Method } call) Call(call, binder);
                else Line($"let {binder} = {Expr(d.Init)};");

                var local = new Slot(d.Name, oc, SlotKind.Object, binder);
                _slots[d.Name] = local;
                _objectLocals.Add(local);
                return;
            }

            case IrBlock b:
                Scoped(() => Sequence(b.Statements, plan), dropAtEnd: true);
                return;

            case IrLocalDecl d:
                LocalDeclaration(d);
                return;

            case IrAssign a:
                Assign(a);
                return;

            case IrIf i:
                If(i, plan);
                return;

            case IrWhile w:
                While(w, plan);
                return;

            case IrGhostStmt g:
                Ghost(g, plan);
                return;

            case IrExprStmt e:
                Line(Expr(e.Expr) + ";");
                return;

            case IrReturn r:
                diagnostics.Unsupported(r.Loc, "A `return` in this position");
                return;

            case IrBreak b2:
                if (_escape?.Break is { } brkCell) Line($"{brkCell} := true;");
                else diagnostics.Unsupported(b2.Loc, "`break` outside a loop");
                if (_escape?.Continue is { } brkEsc) Line($"{brkEsc} := true;");
                return;

            case IrContinue c2:
                if (_escape?.Continue is { } contCell) Line($"{contCell} := true;");
                else diagnostics.Unsupported(c2.Loc, "`continue` outside a loop");
                return;

            default:
                diagnostics.Unsupported(stmt.Loc, $"`{stmt.GetType().Name}`");
                return;
        }
    }

    /// <summary>
    /// R5.10. A statement sequence, with the escape guard threaded through it.
    ///
    /// <para>Pulse has no <c>break</c> and no <c>continue</c>, so the *remainder* of a
    /// sequence after a statement that may escape is emitted under a test of the escape
    /// flags. The rewrite is compositional — it looks only at the statement in hand and
    /// the statements after it — and it is inserted only where <see cref="MayEscape"/>
    /// holds, so a loop without <c>break</c> or <c>continue</c> is emitted exactly as
    /// before.</para>
    /// </summary>
    private void Sequence(ImmutableArray<IrStmt> statements, MethodPlan plan)
    {
        for (var k = 0; k < statements.Length; k++)
        {
            Statement(statements[k], plan);

            var rest = statements.RemoveRange(0, k + 1);
            if (rest.IsEmpty || _escape is null || !MayEscape(statements[k])) continue;

            Line($"if ({EscapeTest()}) {{");
            _indent++;
            Sequence(rest, plan);
            Line("()");
            _indent--;
            Line("} else { () };");
            return;
        }
    }

    /// <summary>
    /// Emits the reads of the escape flags and returns the pure test meaning
    /// "this iteration has not escaped". The flags are read into `let`-bound names because
    /// a Pulse <c>if</c> condition must be pure.
    /// </summary>
    private string EscapeTest()
    {
        var parts = new List<string>();
        foreach (var cell in new[] { _escape!.Break, _escape.Continue })
        {
            if (cell is null) continue;
            var t = Fresh();
            Line($"let {t} = !{cell};");
            parts.Add($"not {t}");
        }
        return string.Join(" && ", parts);
    }

    /// <summary>
    /// Whether <paramref name="stmt"/> can transfer control out of the sequence it is in.
    /// The walk deliberately stops at a nested loop, whose own <c>break</c> and
    /// <c>continue</c> bind to that loop.
    /// </summary>
    private static bool MayEscape(IrStmt stmt) => stmt switch
    {
        IrBreak or IrContinue => true,
        IrBlock b => b.Statements.Any(MayEscape),
        IrIf i => MayEscape(i.Then) || (i.Else is not null && MayEscape(i.Else)),
        _ => false,
    };

    /// <summary>R5.2. Every C# local is a Pulse <c>ref</c> cell.</summary>
    private void LocalDeclaration(IrLocalDecl d)
    {
        var cell = Names.Local(d.Name);
        _slots[d.Name] = new Slot(d.Name, d.Type, SlotKind.Cell, cell);
        var init = d.Init is null ? Default(d.Type) : Expr(d.Init);
        Line($"let mut {cell} = {init};");
    }

    private static string Default(IrType type) => type switch
    {
        IrPrim { Kind: PrimKind.Bool } => "false",
        IrPrim p when p.IsMachineInt => Types.Literal(0, p),
        _ => "(default_of _)",
    };

    /// <summary>R5.3.</summary>
    private void Assign(IrAssign a)
    {
        switch (a.Target)
        {
            case IrVar v when _slots.TryGetValue(v.Name, out var slot) && slot.Kind is SlotKind.Cell or SlotKind.RefParam:
                if (ReadOnly(slot, a.Loc)) return;
                Line($"{slot.Binder} := {Expr(a.Value)};");
                return;

            case IrElement { Array: IrVar av } when
                _slots.TryGetValue(av.Name, out var arr) && ReadOnly(arr, a.Loc):
                return;

            case IrElement el:
            {
                // C# evaluates the target's index before the right-hand side, so the
                // lifted bindings must appear in that order.
                var array = Expr(el.Array);
                var index = Expr(el.Index);
                var value = Expr(a.Value);
                Line($"write {array} {index} {value};");
                return;
            }

            // R3.8. Writing a field of an object is a write through the box: read the
            // representation, replace one field, write it back. The record update needs a
            // pure source (F11), which is why the dereference is let-bound first.
            case IrField { Receiver: IrVar ov } field when
                _slots.TryGetValue(ov.Name, out var obj) && obj is { Kind: SlotKind.Object, Type: IrClassType oc }:
            {
                var value = Expr(a.Value);
                var current = Fresh();
                Line($"let {current} = B.op_Bang {obj.Binder};");
                Line($"B.op_Colon_Equals {obj.Binder} " +
                     $"({{ {current} with {Names.ClassProjection(oc.Name, field.Field)} = {value} }});");
                return;
            }

            // R3.6. A C# field assignment on a value type replaces the whole value, so
            // it becomes an update of the cell the value lives in.
            case IrField field when Root(field) is { } root &&
                                    _slots.TryGetValue(root.Name, out var cell) &&
                                    cell.Kind is SlotKind.Cell or SlotKind.RefParam:
            {
                if (ReadOnly(cell, a.Loc)) return;
                var value = Expr(a.Value);
                var current = Fresh();
                Line($"let {current} = !{cell.Binder};");
                Line($"{cell.Binder} := {Update(current, field, value, a.Loc)};");
                return;
            }

            default:
                diagnostics.Unsupported(a.Loc, "This assignment target");
                return;
        }
    }

    /// <summary>The local or parameter a field path is rooted at, if it is rooted at one.</summary>
    private static IrVar? Root(IrExpr expr) => expr switch
    {
        IrVar v => v,
        IrField f => Root(f.Receiver),
        _ => null,
    };

    /// <summary>
    /// R3.6. Rebuilds a value with one field path replaced. Nested paths compose: `x.f.g`
    /// updates `f` with an update of `g`. The source of a record update must be a pure
    /// term (F11), which is why the caller let-binds the dereference first.
    /// </summary>
    private string Update(string root, IrExpr target, string value, IrLoc loc)
    {
        if (target is not IrField field) return value;

        if (field.Receiver.Type is not IrNamedType named)
        {
            diagnostics.Unsupported(loc, $"The assignment target `.{field.Field}`");
            return value;
        }

        var updated =
            $"{{ {Path(root, field.Receiver, loc)} with {Names.Projection(named.Name, field.Field)} = {value} }}";
        return Update(root, field.Receiver, updated, loc);
    }

    /// <summary>The pure projection path from a root binder down to a field access.</summary>
    private string Path(string root, IrExpr expr, IrLoc loc)
    {
        if (expr is IrVar) return root;
        if (expr is IrField f && f.Receiver.Type is IrNamedType named)
            return $"{Path(root, f.Receiver, loc)}.{Names.Projection(named.Name, f.Field)}";
        diagnostics.Unsupported(loc, "This assignment target");
        return root;
    }

    /// <summary>
    /// R4.9. A slot held at a fractional permission may be observed but not written; the
    /// permission is precisely the right to read.
    /// </summary>
    private bool ReadOnly(Slot slot, IrLoc loc)
    {
        if (slot.Fraction is null) return false;
        diagnostics.Error("PALCS0305", loc,
            $"`{slot.Name}` is held at the fractional permission `{slot.Fraction}` " +
            "and so cannot be written. Remove its `[Frac]` to take full ownership.");
        return true;
    }

    /// <summary>R5.4. Both branches are always emitted.</summary>
    private void If(IrIf i, MethodPlan plan)
    {
        var cond = Expr(i.Cond);
        Line($"if ({cond}) {{");
        _indent++;
        Statement(i.Then, plan);
        Line("()");
        _indent--;
        Line("} else {");
        _indent++;
        if (i.Else is not null) Statement(i.Else, plan);
        Line("()");
        _indent--;
        Line("};");
    }

    /// <summary>R5.6, R5.8, R5.8b, R5.9.</summary>
    private void While(IrWhile w, MethodPlan plan)
    {
        // R5.12. The unfolded receiver is not among the ordinary live slots: inside R4.10's
        // window it is a representation, not an object, and its folded invariant is exactly
        // the thing that does not hold here.
        var live = w.Live.Where(n => _slots.TryGetValue(n, out var s) && s.Owns)
            .Select(n => _slots[n])
            .Where(s => !_objects.Any(o => o.Name == s.Name))
            .ToImmutableArray();
        var unassigned = w.Unassigned.ToImmutableHashSet();

        // Name the values the loop will *not* change, so the invariant can say they are
        // unchanged rather than merely existentially quantified (R5.8b). Values the loop
        // does change are named too, because a ghost statement in the body may need them.
        var fixedNames = new Dictionary<string, string>();
        var existentials = ImmutableArray.CreateBuilder<string>();
        var resources = ImmutableArray.CreateBuilder<string>();
        var scope = new SpecScope(plan.PreScope) { Pre = plan.PreScope };

        foreach (var slot in live)
        {
            var value = FreshValue(slot.Name);
            fixedNames[slot.Name] = value;
            if (!unassigned.Contains(slot.Name)) existentials.Add(value);
            resources.Add(slot.Resource(value));
            scope.Bind(slot.Name, new Term(value, MethodPlan.KindOf(slot.Type), slot.Type));
        }

        // R5.12. Everything R4.10 opened has to be carried across the loop.
        var pure = ImmutableArray.CreateBuilder<string>();
        var repFixed = new List<(string Name, string Resource)>();
        var measureScope = DerefScope();
        foreach (var receiver in _objects)
            Representation(receiver, w.Body, scope, measureScope, resources, existentials, pure, repFixed);

        // R5.8b, and R5.12 with it: a binder the loop cannot change is *named* before the
        // loop rather than existentially quantified inside it, so that what comes out is
        // known to be what went in. For the receiver that is not an optimisation — a
        // read-only method re-folds its invariant at the model it was handed (R4.11a), and
        // an existentially quantified representation could not possibly satisfy it.
        var fixedAll = repFixed
            .Concat(live.Where(s => unassigned.Contains(s.Name))
                        .Select(s => (Name: fixedNames[s.Name], Resource: s.Resource(fixedNames[s.Name]))))
            .ToList();
        if (fixedAll.Count > 0)
        {
            Line($"with {string.Join(" ", fixedAll.Select(f => f.Name))}. " +
                 $"assert ({string.Join(" ** ", fixedAll.Select(f => f.Resource))});");
        }

        // R5.10. Flags are allocated only for the forms the body actually uses, so a
        // loop with neither `break` nor `continue` is emitted unchanged.
        var brkCell = MayEscape(w.Body) && ContainsBreak(w.Body) ? $"var_brk_{_loop}" : null;
        var contCell = ContainsContinue(w.Body) ? $"var_cont_{_loop}" : null;
        _loop++;
        var outerEscape = _escape;
        _escape = brkCell is null && contCell is null ? null : new Escape(brkCell, contCell);

        if (brkCell is not null)
        {
            Line($"let mut {brkCell} = false;");
            var value = FreshValue("brk");
            existentials.Add(value);
            resources.Add($"R.pts_to {brkCell} {value}");
        }

        var guard = Capture(() => Expr(w.Cond));
        Line("while (");
        _indent++;
        _lines.AddRange(guard.Lines);
        if (brkCell is null)
        {
            Line(guard.Term);
        }
        else
        {
            // The user's guard comes first so that its dereferences stay visible to the
            // body; the break flag is a pure conjunct appended to it.
            var t = Fresh();
            Line($"let {t} = !{brkCell};");
            Line($"({guard.Term}) && not {t}");
        }
        _indent--;
        Line(")");

        pure.AddRange(w.Invariants.Select(i => spec.AsProp(spec.Emit(i, scope))));
        Line("invariant " + MethodPlan.Clause(
            resources.ToImmutable(), pure.ToImmutable(), existentials.ToImmutable()));

        if (w.Decreases is not null)
        {
            var measure = spec.Math(w.Decreases, measureScope);
            // The iteration that breaks need not decrease the user's measure — it exits
            // instead. Adding one while the flag is still clear restores the decrease
            // uniformly, and stays linear: F9 forbids a dereference inside a branch of an
            // `if` in a measure, but not in its condition.
            if (brkCell is not null) measure = $"({measure}) + (if !{brkCell} then 0 else 1)";
            Line($"decreases ({measure})");
        }

        Line("{");
        _indent++;
        if (contCell is not null) Line($"let mut {contCell} = false;");
        Statement(w.Body, plan);
        if (!w.Step.IsEmpty)
        {
            // R5.7 + R5.10. The `for` step runs after a `continue` but not after a
            // `break`, so it sits outside the body's escape guard and under the break
            // flag alone.
            if (brkCell is not null)
            {
                var t = Fresh();
                Line($"let {t} = !{brkCell};");
                Line($"if (not {t}) {{");
                _indent++;
                Sequence(w.Step, plan);
                Line("()");
                _indent--;
                Line("} else { () };");
            }
            else
            {
                Sequence(w.Step, plan);
            }
        }
        Line("()");
        _indent--;
        Line("};");
        _escape = outerEscape;
    }

    private static bool ContainsBreak(IrStmt stmt) => stmt switch
    {
        IrBreak => true,
        IrBlock b => b.Statements.Any(ContainsBreak),
        IrIf i => ContainsBreak(i.Then) || (i.Else is not null && ContainsBreak(i.Else)),
        _ => false,
    };

    private static bool ContainsContinue(IrStmt stmt) => stmt switch
    {
        IrContinue => true,
        IrBlock b => b.Statements.Any(ContainsContinue),
        IrIf i => ContainsContinue(i.Then) || (i.Else is not null && ContainsContinue(i.Else)),
        _ => false,
    };

    /// <summary>
    /// The scope a <c>decreases</c> measure is read in: by F3 a measure may dereference
    /// mutable locals but may not mention the invariant's existentials, so every cell
    /// denotes <c>!var_x</c> here rather than a value binder.
    /// </summary>
    private SpecScope DerefScope()
    {
        var scope = new SpecScope();
        foreach (var (name, slot) in _slots)
        {
            var text = slot.Kind is SlotKind.Cell or SlotKind.RefParam ? $"!{slot.Binder}" : slot.Binder;
            // Here an array denotes the live array, not its contents: a measure may
            // dereference a mutable local (F3) but may not mention the invariant's
            // existentials, which is where the contents live.
            var kind = slot.Kind is SlotKind.Array ? TermKind.Array : MethodPlan.KindOf(slot.Type);
            scope.Bind(name, new Term(text, kind, slot.Type));
        }
        return scope;
    }

    /// <summary>
    /// R5.11. A ghost statement needs to name the values held right now, so each one is
    /// preceded by a <c>with … assert …</c> that binds them. Regenerating the names at
    /// every ghost point is what keeps them from going stale after an assignment.
    /// </summary>
    private void Ghost(IrGhostStmt g, MethodPlan plan)
    {
        // R5.13 is handled before the naming bracket below, and deliberately. That bracket
        // names every owned resource at the permission the slot was declared with; a
        // `Share` is the statement that stops that being true, so a lemma about the
        // permission must not be preceded by an assertion that presumes it.
        if (g.Kind is GhostKind.Share or GhostKind.Gather) { Permission(g); return; }

        // R5.12, again: inside R4.10's window the receiver is a representation, so its
        // folded invariant is not what the context holds and asserting it would fail. The
        // representation is named instead, which is also what lets a ghost statement in an
        // instance method mention a field.
        var owned = _slots.Values
            .Where(s => s.Owns && !_objects.Any(o => o.Name == s.Name))
            .ToImmutableArray();
        var scope = new SpecScope(plan.PreScope) { Pre = plan.PreScope };

        var named = new List<(string Name, string Resource)>();
        var here = new IrBlock(g.Loc, ImmutableArray<IrStmt>.Empty);
        foreach (var receiver in _objects)
        {
            Representation(
                receiver, here, scope, new SpecScope(),
                ImmutableArray.CreateBuilder<string>(), ImmutableArray.CreateBuilder<string>(),
                ImmutableArray.CreateBuilder<string>(), named);
        }

        foreach (var slot in owned)
        {
            var value = FreshValue(slot.Name);
            named.Add((value, slot.Resource(value)));
            scope.Bind(slot.Name, new Term(value, MethodPlan.KindOf(slot.Type), slot.Type));
        }

        if (named.Count > 0)
        {
            Line($"with {string.Join(" ", named.Select(n => n.Name))}. " +
                 $"assert ({string.Join(" ** ", named.Select(n => n.Resource))});");
        }

        foreach (var slot in _slots.Values.Where(s => !s.Owns))
            scope.Bind(slot.Name, new Term(slot.Binder, MethodPlan.KindOf(slot.Type), slot.Type));

        switch (g.Kind)
        {
            case GhostKind.Assert:
                Line($"assert (pure ({spec.AsProp(spec.Emit(g.Prop!, scope))}));");
                return;
            case GhostKind.Assume:
                Line($"assume (pure ({spec.AsProp(spec.Emit(g.Prop!, scope))}));");
                return;
            case GhostKind.Raw:
                Line(Antiquotation.Expand(g.Text!, scope) + ";");
                return;
            case GhostKind.LemmaCall when g.Prop is IrCall call:
                Line($"{Names.SpecModule(call.Callee)}.{Names.Lemma(call.Callee)} " +
                     string.Join(" ", call.Args.Select(a => SpecArgument(a, scope))) + ";");
                return;
            default:
                return;
        }
    }

    /// <summary>
    /// R5.13. <c>Pal.Share</c>/<c>Pal.Gather</c> translate by what their argument is: an
    /// object goes through the lemmas R3.10d emitted for its class, an array through
    /// <c>Pulse.Lib.Array</c>'s. Nothing else has a permission to split, so nothing else
    /// has a translation — and that is a translatability refusal, not a provability one:
    /// whether the permission was there to split is Pulse's question.
    /// </summary>
    private void Permission(IrGhostStmt g)
    {
        var share = g.Kind is GhostKind.Share;

        if (g.Prop is IrVar v && Lookup(v.Name) is { } slot)
        {
            switch (slot.Type)
            {
                case IrClassType c:
                    var lemma = share ? Names.ClassInvShare(c.Name) : Names.ClassInvGather(c.Name);
                    Line($"{Names.ClassModule(c.Name)}.{lemma} {slot.Binder};");
                    return;
                case IrArrayType:
                    Line($"A.{(share ? "share" : "gather")} {slot.Binder};");
                    return;
            }
        }

        diagnostics.Unsupported(g.Loc,
            $"`Pal.{(share ? "Share" : "Gather")}` of anything but an array or an object variable");
    }

    private Slot? Lookup(string name) =>
        _slots.TryGetValue(name, out var slot) ? slot
        : _objectLocals.FirstOrDefault(l => l.Name == name);

    /// <summary>
    /// R4.7: a lemma is applied to the values the program holds, so its arguments are
    /// passed with their program types and receive no <c>Int32.v</c> coercion.
    /// </summary>
    private string SpecArgument(IrExpr arg, SpecScope scope) => spec.Emit(arg, scope).Text;

    // =======================================================================
    // Expressions (R6)
    // =======================================================================

    /// <summary>
    /// Emits an expression, let-binding every stateful subexpression, and returns the
    /// Pulse term denoting its value.
    /// </summary>
    private string Expr(IrExpr expr)
    {
        switch (expr)
        {
            case IrLiteral l:
                return Types.Literal(l.Value, l.Type);

            case IrVar v when _slots.TryGetValue(v.Name, out var slot):
                if (slot.Kind is SlotKind.Cell or SlotKind.RefParam)
                {
                    var t = Fresh();
                    Line($"let {t} = !{slot.Binder};");
                    return t;
                }
                return slot.Binder;

            case IrVar v:
                diagnostics.Error("PALCS0400", v.Loc, $"`{v.Name}` is not in scope here.");
                return "()";

            // R6.10: a by-reference argument passes the cell, not its contents.
            case IrRefArg { Operand: IrVar v } when _slots.TryGetValue(v.Name, out var slot)
                                                   && slot.Kind is SlotKind.Cell or SlotKind.RefParam:
                return slot.Binder;

            case IrRefArg r:
                diagnostics.Error("PALCS0402", r.Loc,
                    "Only a local variable or a `ref`/`out` parameter can be passed by reference.");
                return "()";

            case IrLength len:
            {
                var array = Expr(len.Array);
                var t = Fresh();
                Line($"let {t} = length_i32 {array};");
                return t;
            }

            case IrElement el:
            {
                var array = Expr(el.Array);
                var index = Expr(el.Index);
                var t = Fresh();
                Line($"let {t} = read {array} {index};");
                return t;
            }

            // R6.9. `new T[n]`. `Pulse.Lib.CSharp.Array.alloc` is where the garbage
            // collector is assumed: it carries no deallocation obligation, unlike
            // `Pulse.Lib.Array.alloc`, which is a stack allocation.
            case IrNewArray na:
            {
                var length = Expr(na.Length);
                var t = Fresh();
                Line($"let {t} = alloc {length} {Default(na.Element)};");
                return t;
            }

            // R3.8. A field of an object lives behind a box, so reading it is a memory
            // operation, not a projection: the object is dereferenced and the resulting
            // representation projected. Legal only between the opening `unfold` and the
            // closing `fold`, which is exactly where a method body lives.
            case IrField { Receiver: IrVar ov } f when
                _slots.TryGetValue(ov.Name, out var obj) && obj is { Kind: SlotKind.Object, Type: IrClassType oc }:
            {
                var t = Fresh();
                Line($"let {t} = B.op_Bang {obj.Binder};");
                return $"{t}.{Names.ClassProjection(oc.Name, f.Field)}";
            }

            case IrField f:
            {
                // R3.5. A field read of a value type is a pure projection: no memory is
                // touched beyond whatever reading the receiver already required.
                var receiver = Expr(f.Receiver);
                if (f.Receiver.Type is not IrNamedType named)
                {
                    diagnostics.Unsupported(f.Loc, $"The field access `.{f.Field}`");
                    return "()";
                }
                return $"{receiver}.{Names.Projection(named.Name, f.Field)}";
            }

            case IrNew n:
            {
                var fields = n.Fields.Select((f, i) =>
                    (i == 0 ? Names.Projection(n.Struct, f.Field) : Names.Field(f.Field))
                    + " = " + Expr(f.Value)).ToImmutableArray();
                return "{ " + string.Join("; ", fields) + " }";
            }

            case IrUnary u:
                return Unary(u);
            case IrBinary b:
                return Binary(b);

            case IrConditional c:
            {
                var cond = Expr(c.Cond);
                var whenTrue = Capture(() => Expr(c.Then));
                var whenFalse = Capture(() => Expr(c.Else));
                return Branch(cond, whenTrue, whenFalse);
            }

            case IrCall { Kind: CalleeKind.Method } call:
                return Call(call, Fresh());

            case IrConvert cv:
                return Convert(cv);

            default:
                diagnostics.Unsupported(expr.Loc, $"`{expr.GetType().Name}` in executable code");
                return "()";
        }
    }

    /// <summary>Emits a call, binding its result to <paramref name="binder"/>.</summary>
    private string Call(IrCall call, string binder)
    {
        var args = call.Args.Select(Expr).ToImmutableArray();
        // R9.12. A call resolved to an `abstract` declaration is a virtual call: it goes
        // to the dispatching wrapper, which recovers the object and runs its vtable slot.
        // Nothing else about the call changes — the arguments, the implicit model binder
        // and the permission are found by the same rules as for a direct call, because
        // R9.9 gives the wrapper the same contract shape a direct method has.
        var callee = PulseEmitter.DispatchOwner(classes, call.Callee) is { } owner
            ? Names.Dispatch(owner, Names.Member(call.Callee, owner))
            : Names.Function(call.Callee);
        Line($"let {binder} = {callee} " +
             (args.Length == 0 ? "()" : string.Join(" ", args)) + ";");
        return binder;
    }

    private string Unary(IrUnary u)
    {
        var operand = Expr(u.Operand);
        var module = Types.Module((u.Operand.Type as IrPrim)?.Kind ?? PrimKind.Int);
        return u.Op switch
        {
            UnOp.Not => $"(not {operand})",
            UnOp.Neg => $"({module}.sub {Types.Literal(0, u.Operand.Type)} {operand})",
            UnOp.BitNot => $"({module}.lognot {operand})",
            _ => operand,
        };
    }

    private string Binary(IrBinary b)
    {
        // R6.3. `&&` and `||` short-circuit, so the right operand is evaluated inside a
        // branch. This is the ordinary compositional expansion, used identically in a
        // loop guard, an `if` condition and an assignment's right-hand side.
        if (b.Op is BinOp.And or BinOp.Or)
        {
            var left = Expr(b.Left);
            var right = Capture(() => Expr(b.Right));
            var shortCircuit = new Captured([], b.Op == BinOp.And ? "false" : "true");
            return b.Op == BinOp.And
                ? Branch(left, right, shortCircuit)
                : Branch(left, shortCircuit, right);
        }

        var l = Expr(b.Left);
        var r = Expr(b.Right);
        var module = Types.Module((b.Left.Type as IrPrim)?.Kind ?? PrimKind.Int);

        var op = b.Op switch
        {
            BinOp.Add => "add", BinOp.Sub => "sub", BinOp.Mul => "mul",
            BinOp.Div => "div", BinOp.Rem => "rem",
            BinOp.BitAnd => "logand", BinOp.BitOr => "logor", BinOp.BitXor => "logxor",
            BinOp.Shl => "shift_left", BinOp.Shr => "shift_right",
            BinOp.Lt => "lt", BinOp.Le => "lte", BinOp.Gt => "gt", BinOp.Ge => "gte",
            BinOp.Eq => "eq", BinOp.Ne => "eq",
            _ => null,
        };

        if (op is null)
        {
            diagnostics.Unsupported(b.Loc, $"The operator `{b.Op}` in executable code");
            return "()";
        }

        // Booleans have no machine-integer module; they use F*'s own operators.
        if (b.Left.Type is IrPrim { Kind: PrimKind.Bool })
        {
            return b.Op switch
            {
                BinOp.Eq => $"({l} = {r})",
                BinOp.Ne => $"(not ({l} = {r}))",
                _ => $"({l} {(b.Op == BinOp.BitAnd ? "&&" : "||")} {r})",
            };
        }

        var call = $"({module}.{op} {l} {r})";
        return b.Op == BinOp.Ne ? $"(not {call})" : call;
    }

    private string Convert(IrConvert cv)
    {
        var operand = Expr(cv.Operand);
        var from = (cv.Operand.Type as IrPrim)?.Kind;
        var to = (cv.Target as IrPrim)?.Kind;
        if (from == to) return operand;

        diagnostics.Unsupported(cv.Loc, $"The conversion from `{from}` to `{to}`",
            "Numeric conversions are not yet translated.");
        return operand;
    }

    // =======================================================================
    // Capturing sub-blocks
    // =======================================================================

    private readonly record struct Captured(ImmutableArray<EmittedLine> Lines, string Term);

    /// <summary>
    /// Emits into a scratch buffer, so that a sub-block's let-bindings can be placed
    /// inside the branch or guard they belong to rather than hoisted out of it —
    /// hoisting would change evaluation order.
    /// </summary>
    private Captured Capture(Func<string> emit)
    {
        var saved = _lines.Count;
        var term = emit();
        var captured = _lines.GetRange(saved, _lines.Count - saved);
        _lines.RemoveRange(saved, _lines.Count - saved);
        return new Captured([.. captured], term);
    }

    /// <summary>
    /// A two-armed branch used as a value. Pulse permits this in any position, so
    /// short-circuiting needs no flag encoding (fact F8).
    /// </summary>
    private string Branch(string cond, Captured whenTrue, Captured whenFalse)
    {
        if (whenTrue.Lines.Length == 0 && whenFalse.Lines.Length == 0)
            return $"(if {cond} then {whenTrue.Term} else {whenFalse.Term})";

        var t = Fresh();
        Line($"let {t} = if ({cond}) {{");
        _indent++;
        _lines.AddRange(whenTrue.Lines);
        Line(whenTrue.Term);
        _indent--;
        Line("} else {");
        _indent++;
        _lines.AddRange(whenFalse.Lines);
        Line(whenFalse.Term);
        _indent--;
        Line("};");
        return t;
    }
}

/// <summary>PAL's <c>$(…)</c> antiquotation, reused verbatim.</summary>
public static class Antiquotation
{
    public static string Expand(string text, SpecScope scope)
    {
        var sb = new StringBuilder();
        for (var i = 0; i < text.Length; i++)
        {
            if (text[i] != '$' || i + 1 >= text.Length || text[i + 1] != '(')
            {
                sb.Append(text[i]);
                continue;
            }

            var depth = 0;
            var start = i + 2;
            var j = start;
            for (; j < text.Length; j++)
            {
                if (text[j] == '(') depth++;
                else if (text[j] == ')' && depth-- == 0) break;
            }

            var name = text[start..j].Trim();
            sb.Append(scope.TryGet(name, out var term) ? term.Text : name);
            i = j;
        }
        return sb.ToString();
    }
}
