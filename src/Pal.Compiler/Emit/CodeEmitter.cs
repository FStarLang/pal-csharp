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
    IReadOnlyDictionary<string, IrClass>? classes = null,
    IReadOnlyDictionary<string, string>? overrides = null,
    HashSet<string>? slots = null,
    IReadOnlyDictionary<string, ImmutableHashSet<int>>? consumed = null)
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
    /// R10.7. The <c>intro_cons</c> owed by each null test currently open, innermost last.
    /// A recursive object is opened by the <em>null test the C# already writes</em>, exactly
    /// as an ordinary receiver is opened by R4.10's bracket, and like that bracket it has to
    /// be closed on every path out of the branch — including a <c>return</c> in the middle
    /// of it, which is why this is a stack rather than a line emitted after the branch.
    /// </summary>
    private readonly List<string> _windows = [];

    /// <summary>
    /// R4.10. The objects this method holds, in declaration order. Each is unfolded once
    /// on entry and re-folded on every exit; between the two the body owns the
    /// representation and may read and write fields.
    /// </summary>
    private ImmutableArray<Slot> _objects = ImmutableArray<Slot>.Empty;

    // The slots that came from the signature. Their invariants appear in this method's
    // own postcondition, so they are the ones a conversion may not give away (R9.15).
    private ImmutableDictionary<string, Slot> _params = ImmutableDictionary<string, Slot>.Empty;

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

    /// <summary>The plan of the method being emitted, needed by R13.3's prelude.</summary>
    private MethodPlan? _plan;

    public string EmitBody(IrMethod method, MethodPlan plan)
    {
        _plan = plan;
        // In declaration order, not `plan.Slots`': see MethodPlan.SlotOrder. `_slots` is
        // a plain Dictionary, so every later walk of it inherits the order set here.
        foreach (var name in plan.SlotOrder) _slots[name] = plan.Slots[name];

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
        _params = plan.Slots;
        _objects = method.DeclaringClass is not null &&
                   plan.Slots.TryGetValue(Names.This, out var self) &&
                   self.Kind == SlotKind.Object
            ? [self]
            : [];

        // R4.10c. Opened only if the body actually names a field, because a call on `this`
        // needs the invariant *folded* -- that is what the callee's contract requires. A
        // method that only delegates (`int Again() => Get();`, and every computed property
        // that reads through another one, R9.20) touches no field, so opening the bracket
        // around it would hand the callee a representation where it expects an invariant.
        // The comment above has always said the bracket goes where the field accesses are;
        // this is what makes it true.
        if (!TouchesFields(method)) _objects = [];
        else if (_objects.Length > 0 && SelfCall(method) is { } selfCall)
        {
            // R4.10c, the other half. The bracket has one shape, and the two demands are
            // opposite: a field access needs the invariant *unfolded* and a call on `this`
            // needs it *folded*, because that is what the callee's contract asks for.
            // Closing the bracket around the call would be a proof step the emitter
            // invented — R4.11a's fold has to hold of the state at the fold point, and a
            // mutator's intermediate state is exactly where it does not (R3.10's `Shift`).
            // So this is refused, not approximated; before it was emitted, ill-typed, with
            // no diagnostic at all.
            diagnostics.Error("PALCS0597", selfCall.Loc,
                $"`{Unqualify(method.Name, method.DeclaringClass)}` reads a field of " +
                $"`{method.DeclaringClass}` and also calls " +
                $"`{Unqualify(selfCall.Callee, method.DeclaringClass)}` on the same object. " +
                "The field access needs the invariant " +
                "unfolded and the call needs it folded (doc/translation.md R4.10c), and one " +
                "body cannot have it both ways. Read the field through the method, or inline " +
                "the callee.");
        }

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
        else EndOfMethod(method, plan);
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
                var text = Inject(method.ReturnType, ret.Value!, Expr(ret.Value!));
                if (!NeedsEpilogue) { Line(text); return; }

                // A returned object must keep the binder the callee produced it under:
                // re-binding it would leave the context holding its invariant under the
                // old name, which the frame rule cannot match (Error 228). Everything else
                // is let-bound so the epilogue can be interposed before the block's value.
                if (IsObjectBinder(text))
                {
                    if (_objectLocals.FirstOrDefault(l => l.Binder == text) is { Index: not null } ix)
                        Forget(ix);
                    CloseObjects(method, plan, text);
                    Line(text);
                    return;
                }

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
                if (NullTest(i.Cond) is { } window)
                {
                    NullWindow(window, i, branch => Tail(branch!, method, plan), tail: true);
                    return;
                }
                if (i.Cond is IrBinary pnb && PlainNullTest(pnb) is { } ptest)
                {
                    PlainNullWindow(ptest, i, branch => Tail(branch!, method, plan), tail: true);
                    return;
                }
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
                // The block's value is not the statement above it: it is the point at which
                // the method's postcondition is proved. Attributing it to the last statement
                // reads as an accusation against a statement that is very often fine --
                // `test/pulse_refusals/cases/BorrowNotReturned.cs` writes through a span, and
                // it is the *method* that then cannot state anything about the array. So the
                // epilogue is located at the method, where an unprovable postcondition
                // belongs. An explicit `return` keeps its own location, because there the
                // user did write the exit.
                EndOfMethod(method, plan);
                return;
        }
    }

    /// <summary>
    /// The implicit exit at the bottom of a body: close any open objects and give the block
    /// its unit value, both located at the method rather than at whatever statement happened
    /// to come last.
    /// </summary>
    private void EndOfMethod(IrMethod method, MethodPlan plan)
    {
        var outer = _loc;
        _loc = method.Loc;
        try
        {
            if (NeedsEpilogue) CloseObjects(method, plan);
            if (IsVoid(method)) Line("()");
        }
        finally { _loc = outer; }
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
        // R9.21a. An open class's constructor keeps the return type the user declared, so
        // every `new C(…)` is untouched, and allocates the generated leaf. The two are
        // reconciled once, here, by the ordinary upcast (R9.15) -- the same step the reader
        // would get from `C c = new C__impl(…)` written out.
        var allocated = method.ConstructsLeaf is { } leafName ? new IrClassType(leafName) : built;
        Construct(method, built, allocated);
    }

    private void Construct(IrMethod method, IrClassType built, IrClassType alloc)
    {
        if (classes is null || !classes.TryGetValue(alloc.Name, out var decl))
        {
            // The class is missing because the frontend refused it, and that refusal is the
            // diagnostic the user needs. Reporting the constructor too names a symptom of a
            // cause already reported, and sends the reader to the wrong line.
            if (!diagnostics.HasErrors)
                diagnostics.Unsupported(method.Loc, $"A constructor of `{built.Name}`");
            return;
        }

        // R4.12c. `C(…) : this(args)` with nothing after it *is* the chained constructor's
        // result, so it emits that call and returns it. The object comes back with its
        // invariant folded, which is what this function's own postcondition asks for, so
        // there is nothing between the call and the return -- R9.15d, and the same shape
        // any method returning a class has.
        var statements = method.Body is IrBlock b ? b.Statements : [method.Body!];
        if (statements is [IrExprStmt { Expr: IrCall chained }, ..])
        {
            if (statements.Length > 1)
            {
                // Not R4.10c's mixed case but its twin: the chained constructor hands back
                // a folded object, and an assignment after it needs the fields, so the
                // remaining body would have to reopen an invariant this function never
                // established. Refusing beats choosing an unfold point for the user.
                diagnostics.Error("PALCS0598", statements[1].Loc,
                    $"`{built.Name}` chains to another constructor and then does more work. " +
                    "The chained constructor returns the object with its invariant already " +
                    "established (doc/translation.md R4.12c), so a later assignment would have " +
                    "to reopen it, and this constructor is not the one that closed it. Move the " +
                    "work into the constructor being chained to, or assign every field here " +
                    "instead of chaining.");
                return;
            }
            Line($"{Expr(chained)}");
            return;
        }

        var initialisers = new Dictionary<string, string>();
        foreach (var stmt in statements)
        {
            if (stmt is IrAssign { Target: IrField { Receiver: IrVar { Name: Names.This } } f } a)
            {
                initialisers[f.Field] = Expr(a.Value);
                continue;
            }
            // R9.21c. `D(…) : base(args)` is inlined by binding the base constructor's
            // parameters to the arguments and then running its assignments, so a leading
            // `let` is part of a constructor body. Nothing else is: an assignment still
            // may not run before the invariant holds.
            if (stmt is IrLocalDecl { Init: not null } d && initialisers.Count == 0)
            {
                var bound = Names.Local(d.Name);
                Line($"let {bound} = {Inject(d.Type, d.Init, Expr(d.Init))};");
                _slots[d.Name] = new Slot(d.Name, d.Type, SlotKind.Value, bound);
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
        // R10.6b. `new` never returns null in C#, and under R10.2 that is a *typing*
        // obligation rather than a fact about the encoding: the constructor returns
        // `class_C`, the non-null refinement, while `B.alloc` returns `class_C__opt`.
        // The step that bridges them is `B.pts_to_not_null`, a Pulse library lemma
        // applied to the `pts_to` the allocation just produced. The emitter is not
        // inventing a proof here — it is discharging, once and uniformly, the C#
        // guarantee that the surface type already states.
        Line($"B.pts_to_not_null {Names.Result};");

        // R10.6a. Allocation is the one place a new cell enters the induction, and R10.4's
        // `intro_cons` is R3.10b's `fold` — the sub-object's invariant is already in the
        // context, because R4.12b's caller gave it away when it passed the reference.
        if (decl.Recursion is not null)
        {
            Line($"{Names.ClassModule(decl.Name)}.{Names.ClassIntro(decl.Name)} {Names.Result};");
            Line(Names.Result);
            return;
        }

        var slot = new Slot(Names.This, alloc, SlotKind.Object, Names.Result)
        {
            PreModel = null,
            PostModel = "post_" + Names.This,
        };
        Line($"fold {Inv(alloc)} {Names.Result} {ModelWitness(decl, slot)};");
        if (alloc.Name != built.Name)
        {
            var up = Fresh();
            // R9.16. The conversion keeps the index, and a *returned* reference wants the
            // plain invariant -- which is what this constructor's own postcondition, and
            // every `new C(…)` in the program, is written against.
            if (UpcastChain(alloc.Name, Names.Result, null, null, built, Names.This, up)
                is { Index: not null } ix)
                Line($"{Names.ClassModule(built.Name)}.{Names.ClassForgetImpl(built.Name)} " +
                     $"{up} {ix.Index};");
            Line(up);
            return;
        }
        Line(Names.Result);
    }


    /// <summary>Resolves <c>$&amp;(x)</c> to the Pulse name holding <c>x</c>.</summary>
    private string? Binder(string name) =>
        _slots.TryGetValue(name, out var slot) ? slot.Binder : null;

    private bool IsObjectBinder(string text) =>
        _objectLocals.Any(l => l.Binder == text) || _objects.Any(o => o.Binder == text) ||
        // R10.6b. A method may hand back an object it was *given*, which is what a
        // traversal that returns one of its arguments does. The binder rule is the same:
        // re-binding it would leave the invariant in the context under the old name.
        _slots.Values.Any(s => s.Kind is SlotKind.Object && s.Binder == text) ||
        // R10.6c. A call's result is held under the binder the call bound it to.
        _objectResults.Contains(text);

    /// <summary>R10.6c. Binders that a call produced an object under.</summary>
    private readonly HashSet<string> _objectResults = new(StringComparer.Ordinal);

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
                var subResource = PulseEmitter.SubInvAt(f.Type, projection, receiver.PermArg, sub);
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
    /// R9.18. The base classes between <paramref name="derived"/> and
    /// <paramref name="ancestor"/>, nearest first and <paramref name="ancestor"/> last, or
    /// <c>null</c> if it is not one. The chain is what makes a conversion across several
    /// levels the composition of the one-edge rule rather than a rule of its own.
    /// </summary>
    private ImmutableArray<string>? Ancestors(string? derived, string? ancestor)
    {
        if (derived is null || ancestor is null || classes is null) return null;
        var chain = ImmutableArray.CreateBuilder<string>();
        for (var at = derived; classes.TryGetValue(at, out var c) && c.BaseClass is { } up;)
        {
            chain.Add(up);
            if (up == ancestor) return chain.ToImmutable();
            at = up;
        }
        return null;
    }

    /// <summary>
    /// R9.15. The upcast, wherever C# inserts a reference conversion: the object is held
    /// at its own class, its invariant is read at the base's model through R9.14's view,
    /// and the conversion returns the reference the base-typed context is given.
    ///
    /// <para>It is written once and used at every conversion site — a local declaration,
    /// an argument, a <c>return</c> — because that is what the frontend now records
    /// (R9.15) and what makes those three positions the same rule rather than three.</para>
    ///
    /// <para>The conversion <b>consumes</b> the derived reference. C# would leave both
    /// names usable, but the derived object's invariant *becomes* the base's, so the old
    /// name owns nothing afterwards; it is marked cast, and PALCS0548 says so at the next
    /// use rather than letting Pulse fail on a resource that is no longer there.</para>
    /// </summary>
    private Slot? Upcast(IrLoc loc, IrExpr operand, IrClassType target, string name, string binder)
    {
        var derived = (operand.Type as IrClassType)?.Name;

        // R9.18. C# writes one conversion where the hierarchy has several edges, and the
        // translation writes one per edge: a conversion to a base is the composition of the
        // conversions along the chain, in order. That is the one-edge rule applied
        // repeatedly and nothing else — the intermediate references are the same ones the
        // reader would get by writing the conversions out.
        if (Ancestors(derived, target.Name) is not { } chain)
        {
            diagnostics.Unsupported(loc,
                $"Converting a `{derived}` to a `{target.Name}`",
                "R9.15 converts a reference to a base class, and `" + target.Name +
                "` is not one of `" + derived + "`'s.");
            return null;
        }

        string impl;
        string? from = null;
        // R9.15e. A chain may be walked in pieces — `Rect r = new Rect__impl(6);` then
        // `AtMiddle(r)` is two conversions over one value — so the name the earlier piece
        // bound the model under is picked up from the slot, exactly as the index is.
        string? held = null;
        if (operand is IrVar v && Lookup(v.Name) is { Kind: SlotKind.Object } src)
        {
            // R9.15c. The conversion *moves* the invariant onto the base reference, so a
            // method that converts one of its own parameters no longer owns what R4.10's
            // epilogue owes back — unless it takes it back with a cast down (R9.16).
            // Which of the two it is, is a separation-logic question about what is owned
            // where, and Pulse is the one that answers it: the epilogue simply cannot be
            // proved. This was briefly PALCS0549 here; see
            // `test/pulse_refusals/cases/UpcastParameter.cs` for why it is not any more.

            impl = src.Binder;
            from = src.Index;
            held = src.PreModel;
            _slots[v.Name] = src with { Kind = SlotKind.Value, Index = null, Cast = target.Name };
            _objectLocals.RemoveAll(l => l.Binder == src.Binder);
        }
        else if (operand is IrCall { Kind: CalleeKind.Method } call) { impl = Fresh(); Call(call, impl); }
        else { impl = Fresh(); Line($"let {impl} = {Expr(operand)};"); }

        return UpcastChain(derived!, impl, from, held, target, name, binder);
    }

    /// <summary>
    /// R9.18. One edge per class boundary, in order. Split out of <see cref="Upcast"/> so
    /// that R9.21a's constructor, which has a binder rather than an expression to convert,
    /// walks the very same chain.
    /// </summary>
    private Slot? UpcastChain(
        string derived, string impl, string? from, string? held,
        IrClassType target, string name, string binder)
    {
        if (Ancestors(derived, target.Name) is not { } chain) return null;
        Slot? slot = null;
        var current = derived;
        for (var i = 0; i < chain.Length; i++)
        {
            var last = i == chain.Length - 1;
            var step = last ? binder : Fresh();
            slot = UpcastStep(current, impl, from, new IrClassType(chain[i]), last ? name : step, step, held);
            impl = step;
            from = slot.Index;
            held = slot.PreModel;
            current = chain[i];
        }
        return slot;
    }

    /// <summary>R9.15, one edge: from <paramref name="derived"/> to its immediate base.</summary>
    /// <param name="held">
    /// R9.15e. The name the previous edge bound this value's model under, when there was
    /// one. A chain of edges has to carry it: each edge names the model it produces, and
    /// the next edge forgets *that* name rather than re-deriving the expression.
    /// </param>
    private Slot UpcastStep(
        string derived, string impl, string? from, IrClassType target, string name, string binder,
        string? held = null)
    {
        var mod = Names.ClassModule(derived);

        // R9.18. An *abstract* class's reference already is a reference: there is no
        // representation to view and no vtable to build, and the conversion changes the
        // invariant and not the value. So the whole of it is the cast R9.18 emits beside
        // the class, and the only choice here is whether the object record is known.
        if (classes is not null && classes[derived].IsAbstract)
        {
            // R9.15e. `Rebase` rewrites `forget` applied to a *name*, so when nothing has
            // named this value's model yet — it came from a call, not from a slot — the
            // name is asked for here. Naming a model the invariant already existentially
            // quantifies is R9.6's `with`, not a proof step.
            if (held is null)
            {
                held = FreshValue(name);
                Line($"with {held}. assert ({mod}.{Names.ClassInv(derived)} {impl} {held});");
            }
            if (from is null)
            {
                Line($"let {binder} = {mod}.{Names.UpcastTo(derived, target.Name)} {impl};");
                return new Slot(name, target, SlotKind.Object, binder)
                {
                    PreModel = Rebase(mod, derived, target, held),
                };
            }
            Line($"let {binder} = {mod}.{Names.UpcastToAt(derived, target.Name)} {impl} {from};");
            return new Slot(name, target, SlotKind.Object, binder)
            {
                Index = $"(hide ({mod}.{Names.ClassView(derived)} (reveal {from})))",
                Sub = from,
                PreModel = Rebase(mod, derived, target, held),
            };
        }

        // The view is folded at the forgetting of whatever model the value is held at,
        // which is the same expression R9.6 read off the `[Model]` override. Only the
        // prover can name that model, which is what the `with` is for: it is the naming
        // R9.6 needs, not a proof step.
        var own = FreshValue(name);
        Line($"with {own}. assert ({mod}.{Names.ClassInv(derived)} {impl} {own});");

        // R9.15e. The forgotten model is bound to a name *of the base's model type* before
        // the fold, rather than left as an application of `forget` inside it. Every class
        // has its own `__model` refinement (R9.5), so a term only known at the derived
        // class's refinement is one the base's spec functions cannot be unfolded on. The
        // reference this cast produces is owned at whatever names its model, and that name
        // is what a later caller's implicit is instantiated with; binding it here is what
        // keeps the base's own vocabulary applicable to it afterwards.
        var basis = FreshValue(target.Name);
        Line($"let {basis} : erased ({Names.ClassModule(target.Name)}.{Names.ClassModel(target.Name)}) = " +
             $"hide ({mod}.{Names.ClassForget(derived)} {own});");
        Line($"fold ({mod}.{Names.ClassAsBase(derived, target.Name)} {impl} (reveal {basis}));");
        Line($"let {binder} = {Names.VtblModule(derived)}." +
             $"{Names.UpcastToAt(derived, target.Name)} {impl};");

        // R9.16. The conversion keeps the index, so the object record this reference
        // stands for stays known and a later cast back is provable. Where the plain
        // invariant is wanted instead, `Forget` drops it — one ghost step, at the point
        // that wants it, and nothing recovers it afterwards.
        var index = $"(hide ({Names.VtblModule(derived)}.{Names.ClassObjOf(derived)} {impl}))";
        return new Slot(name, target, SlotKind.Object, binder) { Index = index, PreModel = basis };
    }

    /// <summary>
    /// R9.15e, for an edge out of an *abstract* class. There is nothing to fold here — the
    /// cast is one generated ghost function (R9.18) whose <c>ensures</c> is written at
    /// <c>class_D__forget m</c> — so the base model cannot be named before it is produced.
    /// It is named after, and the resource moved onto the name.
    ///
    /// <para>The move is what matters. Where the forgetting is the identity, Pulse reduces
    /// <c>class_D__forget m</c> back to <c>m</c> and instantiates a later caller's implicit
    /// with that, which is a term at <em>D</em>'s model refinement and not the base's; the
    /// <c>rewrite each</c> is what stops it, because a binder has no further reduct. It
    /// mentions neither the index nor the permission, so it is the same one step whatever
    /// the reference is held at.</para>
    ///
    /// <para>Returns null only when no name was available at all.</para>
    /// </summary>
    private string? Rebase(string mod, string derived, IrClassType target, string? held)
    {
        if (held is null) return null;
        var basis = FreshValue(target.Name);
        var forgotten = $"({mod}.{Names.ClassForget(derived)} (reveal {held}))";
        Line($"let {basis} : erased ({Names.ClassModule(target.Name)}.{Names.ClassModel(target.Name)}) = " +
             $"hide {forgotten};");
        Line($"rewrite each {forgotten} as (reveal {basis});");
        return basis;
    }

    /// <summary>
    /// R9.15, in expression position. The conversion is a statement — it moves a resource
    /// and binds a new name — so the value it produces is an anonymous object local: owned
    /// here, dropped where the block closes unless it is returned.
    /// </summary>
    private string UpcastExpr(IrConvert cv, IrClassType target)
    {
        var binder = Fresh();
        if (Upcast(cv.Loc, cv.Operand, target, binder, binder) is not { } slot) return "()";
        _objectLocals.Add(slot);
        return binder;
    }

    /// <summary>
    /// R9.16. <c>D x = (D) b;</c>. The cast is justified by <paramref name="source"/>'s
    /// index — the object record it is known to stand for — which is exactly the knowledge
    /// C# would test for at runtime, and which R9.15a's conversion kept. A base reference
    /// with no index is one whose dynamic type the translation does not know, and the cast
    /// is refused rather than emitted for Pulse to fail on.
    ///
    /// <para>The result is handed back at the base's model, through R9.14's view; opening
    /// that view immediately turns it into an ordinary M2 object local, and leaves in
    /// context the equation relating the two models — which is what lets the caller keep
    /// reasoning about the value it cast.</para>
    /// </summary>
    private void Downcast(IrLocalDecl d, IrClassType target, IrVar source, string binder)
    {
        if (Lookup(source.Name) is not { Kind: SlotKind.Object, Type: IrClassType from } obj ||
            Ancestors(target.Name, from.Name) is not { } up)
        {
            diagnostics.Unsupported(d.Loc, $"Casting a `{Lookup(source.Name)?.Type}` to `{target.Name}`",
                "R9.16 casts a reference to a subclass, and `" + target.Name +
                "` is not one of `" + Lookup(source.Name)?.Type + "`'s.");
            return;
        }

        // R9.18, mirroring R9.15's chain: a cast across several levels is the composition
        // of the one-level casts, applied from the base downwards. Each recovers one
        // record, and the knowledge each gives back is the knowledge the matching upcast
        // kept — which is why the last one is the first that can name the leaf's model.
        for (var i = up.Length - 2; i >= 0; i--)
        {
            var step = Fresh();
            if (DowncastStep(d.Loc, obj, new IrClassType(up[i]), step, step) is not { } mid) return;
            _slots[step] = mid;
            _objectLocals.Add(mid);
            obj = mid;
        }

        if (DowncastStep(d.Loc, obj, target, d.Name, binder) is not { } local) return;
        _slots[d.Name] = local;
        _objectLocals.Add(local);
    }

    /// <summary>R9.16, one edge: from <paramref name="obj"/>'s class to its immediate subclass.</summary>
    private Slot? DowncastStep(IrLoc loc, Slot obj, IrClassType target, string name, string binder)
    {
        var source = obj;
        var from = (IrClassType)obj.Type;

        // R9.18. Casting down to an intermediate class needs the record *it* was upcast
        // from, not the one the base reference is indexed by: they are different records,
        // related by the view, and only the first says which quadrilateral this is.
        if (classes is not null && classes[target.Name].IsAbstract ? obj.Sub is null : obj.Index is null)
        {
            diagnostics.Error("PALCS0547", loc,
                $"`{source.Name}` is not known to be a `{target.Name}`, so this cast might " +
                "throw. R9.16 proves only the casts whose runtime test is redundant: the " +
                $"reference must have been converted from a `{target.Name}` in this method.");
            return null;
        }

        // The model the reference is held at has to be named before the cast: the view the
        // cast hands back is indexed by it, and only the prover knows what it is.
        var pre = FreshValue(source.Name);
        Line($"with {pre}. assert ({obj.Resource(pre)});");

        var own = FreshValue(name);
        var mod = Names.ClassModule(target.Name);
        string? sub = null;

        // R9.18. Casting down to an *intermediate* class. The cast lives beside that class
        // rather than in a vtable module, because there is no vtable: what is recovered is
        // the object record the reference was upcast from, which the upcast kept, and the
        // model comes back existentially because forgetting is not injective.
        if (classes is not null && classes[target.Name].IsAbstract)
        {
            sub = obj.Sub;
            Line($"let {binder} = {mod}.{Names.DowncastFrom(target.Name, from.Name)} {obj.Binder};");
            Line($"with {own}. assert ({mod}.{Names.ClassInvAt(target.Name)} " +
                 $"{binder} {sub} {obj.Fraction ?? "1.0R"} {own});");
        }
        else
        {
            Line($"let {binder} = {Names.VtblModule(target.Name)}." +
                 $"{Names.DowncastFrom(target.Name, from.Name)} {obj.Binder};");
            Line($"unfold ({mod}.{Names.ClassAsBase(target.Name, from.Name)} " +
                 $"{binder} {obj.PermArg}{pre});");
            Line($"with {own}. assert ({mod}.{Names.ClassInv(target.Name)} {binder} {obj.PermArg}{own});");
        }

        // The base reference owns nothing now: its invariant *became* the derived one.
        // C# would let it be read again, so saying so is the emitter's job (PALCS0548).
        _slots[source.Name] = obj with { Kind = SlotKind.Value, Index = null, Cast = target.Name };
        _objectLocals.RemoveAll(s => s.Binder == obj.Binder);

        return new Slot(name, target, SlotKind.Object, binder)
        { Fraction = obj.Fraction, PreModel = own, PostModel = own, Index = sub };
    }

    /// <summary>
    /// R9.16. Drops a slot's index, where what wants the resource wants the plain
    /// invariant: an argument at a base-typed parameter, or a returned reference. One
    /// ghost step, and irreversible — which is why it is emitted at the point that needs
    /// it and not at the conversion.
    /// </summary>
    private void Forget(Slot obj)
    {
        // The model is left implicit on purpose. Naming it with a `with` first would bind
        // it to an opaque witness, and everything the context knew about the model — that
        // it is *this* leaf's forgetting of *that* constructor's post-state — would be cut
        // at exactly the point a caller still needs it (F34's lesson, one level up).
        var klass = (IrClassType)obj.Type;
        Line($"{Names.ClassModule(klass.Name)}.{Names.ClassForgetImpl(klass.Name)} " +
             $"{obj.Binder} {obj.Index};");
        var plain = obj with { Index = null };
        _slots[obj.Name] = plain;
        for (var i = 0; i < _objectLocals.Count; i++)
            if (_objectLocals[i].Binder == obj.Binder) _objectLocals[i] = plain;
    }

    /// <summary>
    /// R4.10c. Whether a body names a field of its receiver, which is the only reason to
    /// open the fold/unfold bracket.
    /// </summary>
    /// <remarks>
    /// A constructor is excluded: it builds the representation rather than reading one,
    /// and <see cref="Construct"/> handles it before this point is reached.
    /// </remarks>
    private static bool TouchesFields(IrMethod method) =>
        method.Body is not null
        && Check.Statements(method.Body)
            .SelectMany(Check.Expressions)
            .SelectMany(Check.Subexpressions)
            .Any(e => e is IrField { Receiver: IrVar { Name: var n } } && n == Names.This);

    /// <summary>R2.1's type qualifier removed, so a diagnostic names what the user wrote.</summary>
    private static string Unqualify(string name, string? klass) =>
        klass is not null && name.StartsWith(klass + "_", StringComparison.Ordinal)
            ? name[(klass.Length + 1)..]
            : name;

    /// <summary>
    /// R4.10c. A call on the receiver from inside one of its own methods, if there is one.
    /// </summary>
    private static IrCall? SelfCall(IrMethod method) =>
        method.Body is null ? null
        : Check.Statements(method.Body)
            .SelectMany(Check.Expressions)
            .SelectMany(Check.Subexpressions)
            .OfType<IrCall>()
            .FirstOrDefault(c => c is { HasReceiver: true, Args: [IrVar { Name: var n }, ..] }
                                 && n == Names.This);

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
    private bool NeedsEpilogue => _objects.Length > 0 || _objectLocals.Count > 0 || _windows.Count > 0;

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
        // A slot is a *binding*, and a binding introduced inside a block is out of scope
        // once the block closes. Nothing outside may name it — in particular R5.13's
        // resource-naming bracket, which would otherwise assert `pts_to` for a cell whose
        // Pulse binder no longer exists.
        var declared = new HashSet<string>(_slots.Keys);
        if (dropAtEnd) _closingBlocks++;
        emit();
        if (dropAtEnd) { _closingBlocks--; DropLocals(null, mark); }
        _objectLocals.RemoveRange(mark, _objectLocals.Count - mark);
        foreach (var name in _slots.Keys.Where(n => !declared.Contains(n)).ToList())
            _slots.Remove(name);
    }

    private void DropLocals(string? returned, int from = 0)
    {
        foreach (var local in _objectLocals.Skip(from))
        {
            if (local.Binder == returned) continue;
            var m = FreshValue(local.Name);
            Line($"with {m}. assert ({local.Resource(m)});");
            Line($"drop_ ({local.Resource(m)});");
        }
    }

    private void CloseObjects(IrMethod method, MethodPlan plan, string? returned = null)
    {
        DropLocals(returned);

        // R10.7. The innermost window closes first: it was opened last, and what it
        // re-establishes is a conjunct of what the one outside it re-establishes.
        for (var i = _windows.Count - 1; i >= 0; i--) Line(_windows[i]);

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
                     $"({PulseEmitter.SubInvAt(field.Type, projection, obj.PermArg, subModel)});");
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
            // R12.4. A local naming a `[Plain]` object. An immutable binder rather than
            // R5.2's `let mut` cell: the reference is a value, and the resource behind it
            // is matched by the binder's name, so putting it in a cell would leave every
            // later mention asking for a `pts_to` at a name Pulse cannot see through.
            // R17.5. A span local. Like R12.4's `[Plain]` reference and unlike R5.2's
            // ordinary local, it gets an immutable binder rather than a `let mut` cell:
            // Pulse matches `S.pts_to` by name, so putting the slice in a cell would leave
            // the context holding the resource at a name every later mention has to read
            // through. C# agrees — a `Span<T>` local the subset admits is never reassigned,
            // because a reassignment would abandon a live receipt.
            //
            // The slot records where the borrow came from. That is not flow analysis: it is
            // the shape of the initializer, read once, at the declaration that wrote it.
            case IrLocalDecl { Type: IrSpanType, Init: IrSpanCreate create } d:
            {
                // The borrow is emitted *at* the local's binder rather than at a fresh one
                // it is then copied from, for the reason R12.4 gives for an allocation:
                // Pulse matches resources by name, so a copy would leave the context
                // holding `S.pts_to t0 _` while every later mention asked for
                // `S.pts_to var_s _` (F77).
                var binder = Names.Local(d.Name);
                Borrow(create, binder);
                _slots[d.Name] = new Slot(d.Name, d.Type, SlotKind.Span, binder)
                {
                    Origin = create.Origin,
                };
                return;
            }

            // R17.5. A span local with any other initializer — another span local, a span
            // parameter, a conditional. Each would alias a live borrow under a second name
            // (SliceFacts S4), and the receipt names only one of them.
            case IrLocalDecl { Type: IrSpanType } d:
                diagnostics.SpanWindow(d.Loc,
                    $"a `Span<T>` local initialised from anything but a borrow (`{d.Name}`)");
                return;

            case IrLocalDecl { Type: IrClassType pc, Init: not null } d
                when classes is not null && classes.TryGetValue(pc.Name, out var pdecl) && pdecl.IsPlain:
            {
                var pbinder = Names.Local(d.Name);
                if (d.Init is IrAlloc pal)
                {
                    // The allocation is emitted *at* the local's binder rather than at a
                    // fresh one it is then copied from. Pulse matches resources by name, so
                    // a copy would leave the context holding `pts_to t0 _` while every later
                    // mention asked for `pts_to var_node _` — the same reason R3.8's alias
                    // case shares a slot instead of rebinding one.
                    Line($"let {pbinder} = B.alloc {AllocRecord(pal)};");
                    Line($"B.pts_to_not_null {pbinder};");
                }
                else if (d.Immutable)
                {
                    _slots[d.Name] = new Slot(d.Name, d.Type, SlotKind.Value, Expr(d.Init));
                    return;
                }
                else
                {
                    // R12.3b. A `[Plain]` reference the body *assigns* is a local like any
                    // other, so R5.2 applies unchanged: it gets a `let mut`, and its slot is
                    // a cell whose resource is an ordinary `R.pts_to`. That is what a cursor
                    // is — a reference the loop moves — and it needs no rule of its own,
                    // only the ordinary one not being skipped because the local happens to
                    // hold a reference.
                    Line($"let mut {pbinder} = {Expr(d.Init)};");
                    _slots[d.Name] = new Slot(d.Name, d.Type, SlotKind.Cell, pbinder);
                    return;
                }
                _slots[d.Name] = new Slot(d.Name, d.Type, SlotKind.Value, pbinder);
                return;
            }

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

                // R9.15/R9.16. A reference conversion, which C# writes silently when it
                // goes up and explicitly when it comes back down. The two directions are
                // told apart by the hierarchy, not by the syntax, because `Shape s = sq;`
                // and `Square q = (Square) s;` are the same IR node.
                if (d.Init is IrConvert { Target: IrClassType } conv)
                {
                    var from = (conv.Operand.Type as IrClassType)?.Name;
                    if (Ancestors(from, oc.Name) is not null)
                    {
                        if (Upcast(d.Loc, conv.Operand, oc, d.Name, binder) is { } up)
                        {
                            _slots[d.Name] = up;
                            _objectLocals.Add(up);
                        }
                        return;
                    }

                    if (conv.Operand is IrVar source && Ancestors(oc.Name, from) is not null)
                    {
                        Downcast(d, oc, source, binder);
                        return;
                    }

                    diagnostics.Unsupported(d.Loc,
                        $"Converting a `{from}` to a `{oc.Name}`",
                        "R9.15 converts a reference between a class and its bases; " +
                        "these two are not related that way.");
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
        var init = d.Init is null ? Default(d.Type) : Expr(d.Init);
        if (d.Immutable)
        {
            _slots[d.Name] = new Slot(d.Name, d.Type, SlotKind.Value, cell);
            Line($"let {cell} = {init};");
            return;
        }
        _slots[d.Name] = new Slot(d.Name, d.Type, SlotKind.Cell, cell);
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
                Line($"{(IsSpan(el.Array) ? "Span." : "")}write {array} {index} {value};");
                return;
            }

            // R12.3. Writing a field of a `[Plain]` reference: the same write as R3.8,
            // reached by a different slot kind. This is the operation §10 could not offer
            // at all, because a derived predicate *owns* the field it folds over; here the
            // user's predicate only constrained `prev`, so overwriting it is a plain write
            // and re-closing the segment reports what the field now holds.
            case IrField { Receiver: IrVar wv } wfield when
                _slots.TryGetValue(wv.Name, out var wobj)
                && wobj is { Kind: SlotKind.Value, Type: IrClassType wc }
                && classes is not null && classes.TryGetValue(wc.Name, out var wdecl)
                && wdecl.IsPlain:
            {
                if (!Reachable(wobj, wfield.Loc, wfield.Field)) return;
                var wvalue = Inject(FieldType(wc, wfield.Field), a.Value, Expr(a.Value));
                var wcur = Fresh();
                Line($"let {wcur} = B.op_Bang {wobj.NonNull};");
                Line($"B.op_Colon_Equals {wobj.NonNull} " +
                     $"({{ {wcur} with {Names.ClassProjection(wc.Name, wfield.Field)} = {wvalue} }});");
                return;
            }

            // R3.8. Writing a field of an object is a write through the box: read the
            // representation, replace one field, write it back. The record update needs a
            // pure source (F11), which is why the dereference is let-bound first.
            case IrField { Receiver: IrVar ov } field when
                _slots.TryGetValue(ov.Name, out var obj) && obj is { Kind: SlotKind.Object, Type: IrClassType oc }:
            {
                if (!Reachable(obj, field.Loc, field.Field)) return;
                var value = Inject(FieldType(oc, field.Field), a.Value, Expr(a.Value));
                var current = Fresh();
                Line($"let {current} = B.op_Bang {obj.NonNull};");
                Line($"B.op_Colon_Equals {obj.NonNull} " +
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
            $"({{ {Path(root, field.Receiver, loc)} with {Names.Projection(named.Name, field.Field)} = {value} }})";
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
        if (NullTest(i.Cond) is { } window)
        {
            NullWindow(window, i, branch => { if (branch is not null) Statement(branch, plan); }, tail: false);
            Line(";");
            return;
        }

        if (i.Else is not null && i.Cond is IrBinary pnb && PlainNullTest(pnb) is { } ptest)
        {
            PlainNullWindow(ptest, i, branch => { if (branch is not null) Statement(branch, plan); }, tail: false);
            Line(";");
            return;
        }

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

    /// <summary>
    /// R10.2b. A non-null reference where a nullable one is expected. C# calls this the
    /// identity because nullability is an annotation there, and under R10.2 the encoding
    /// agrees: `C` is `C?` under a refinement. So the *term* is unchanged. What is left is
    /// the invariant, which R10.3a states through an abbreviation Pulse's matcher does not
    /// see through (F77), so `as_opt` survives as a one-line rewrite.
    /// </summary>
    private string Inject(IrType? expected, IrExpr value, string text)
    {
        if (expected is not IrClassType { Nullable: true } k) return text;
        if (value.Type is not IrClassType { Nullable: false } nn || nn.Name != k.Name) return text;
        // R10.2 (F76). The *term* is unchanged: `class_C` is `class_C__opt` under a
        // refinement, so a non-nullable reference already is a nullable one, and C#'s
        // identity coercion is F*'s. What remains is not about the reference but about its
        // invariant, which is stated through R10.3a's abbreviation and must be unfolded.
        // R12.2. A plain reference carries no invariant, so for it there is nothing at all.
        if (classes is not null && classes.TryGetValue(k.Name, out var kd) && kd.IsPlain)
            return text;
        Line($"{Names.ClassModule(k.Name)}.{Names.ClassAsOpt(k.Name)} {text};");
        return text;
    }

    /// <summary>R12.4. The record an allocation boxes.</summary>
    private string AllocRecord(IrAlloc al)
    {
        var flds = al.Record.Fields.Select((f, i) =>
            (i == 0 ? Names.ClassProjection(al.Class, f.Field) : Names.Field(f.Field))
            + " = " + Inject(f.FieldType, f.Value, Expr(f.Value)));
        return "({ " + string.Join("; ", flds) + " })";
    }

    private IrType? FieldType(IrClassType owner, string field) =>
        classes is not null && classes.TryGetValue(owner.Name, out var decl)
            ? decl.Fields.FirstOrDefault(f => f.Name == field)?.Type
            : null;

    /// <summary>
    /// R10.8. Whether the representation behind a reference is reachable here. For a
    /// non-null reference it always is; for a nullable one it is exactly inside the window
    /// R10.7 opens, because that is where the head cell has been given up. Refusing the
    /// rest is not the emitter inventing a refusal: outside a window the reference is still
    /// an `option` and there is no record to project.
    /// </summary>
    private bool Reachable(Slot obj, IrLoc loc, string field)
    {
        if (obj.Type is not IrClassType { Nullable: true } k || obj.Window) return true;
        // R12.3c. For a `[Plain]` class there is no derived invariant and so no window: §12
        // gave the ownership of the record to the user's predicate, and whether it is held
        // here is that predicate's business, not the emitter's. So the projection is
        // emitted and Pulse checks the non-null refinement against whatever the user's
        // annotations establish — a loop guard, a lemma, an `if`. Refusing it here would be
        // the emitter inventing a refusal (§0 rule 3): it would rule out every cursor, and
        // a cursor's null test is a *loop condition*, which no window can be the extent of.
        if (classes is not null && classes.TryGetValue(k.Name, out var d) && d.IsPlain) return true;
        diagnostics.Error("PALCS0567", loc,
            $"`{obj.Name}.{field}` reads through a reference that may be null. A field behind a " +
            "nullable class reference is reachable only inside a null test — write `if (" + obj.Name +
            " == null) { … } else { … }` and reach the field in the `else` branch " +
            "(doc/translation.md R10.7).");
        return false;
    }

    /// <summary>
    /// R12.3. The operand of an <c>== null</c> / <c>!= null</c> test whose static type is a
    /// nullable <c>[Plain]</c> class, or <c>null</c> when this is not such a test.
    /// </summary>
    private (IrExpr Tested, Slot? Slot, bool ThenIsNull)? PlainNullTest(IrBinary b)
    {
        if (b.Op is not (BinOp.Eq or BinOp.Ne)) return null;
        var tested = b.Left is IrNull ? b.Right : b.Right is IrNull ? b.Left : null;
        if (tested?.Type is not IrClassType { Nullable: true } k) return null;
        if (classes is null || !classes.TryGetValue(k.Name, out var decl) || !decl.IsPlain) return null;
        Slot? slot = null;
        if (tested is IrVar v && _slots.TryGetValue(v.Name, out var s) && s.Kind is SlotKind.Value)
            slot = s;
        return (tested, slot, b.Op is BinOp.Eq);
    }

    /// <summary>
    /// R12.3. The bracket R10.7 puts around a null test, with every proof step taken out.
    /// §12 derived no predicate for a <c>[Plain]</c> class, so there is nothing to case
    /// split and no lemma the emitter would be entitled to place; what remains is the
    /// branch itself and the one fact the branch establishes — that in the <c>else</c>
    /// arm the reference is non-null, so the record behind it can be projected. Whether
    /// that projection is <em>owned</em> is the user's predicate's business, and a missing
    /// <c>pts_to</c> is a failure in their annotations rather than in the translation.
    /// </summary>
    private void PlainNullWindow(
        (IrExpr Tested, Slot? Slot, bool ThenIsNull) test, IrIf i,
        Action<IrStmt?> branch, bool tail)
    {
        var opt = Expr(test.Tested);
        var nullBranch = test.ThenIsNull ? i.Then : i.Else;
        var otherBranch = test.ThenIsNull ? i.Else : i.Then;

        Line($"if (B.is_null {opt}) {{");
        _indent++;
        branch(nullBranch);
        if (!tail) Line("()");
        _indent--;
        Line("} else {");
        _indent++;
        var saved = test.Slot is null ? null : _slots[test.Slot.Name];
        if (saved is not null) _slots[saved.Name] = saved with { Window = true };
        try
        {
            branch(otherBranch);
            if (!tail) Line("()");
        }
        finally
        {
            if (saved is not null) _slots[saved.Name] = saved;
        }
        _indent--;
        Line("}");
    }

    /// <summary>
    /// R10.7. A null test on a recursive object, which is where §10 puts the case lemmas.
    /// Returns the slot tested, its class, and whether the <c>then</c> branch is the null
    /// one — nothing else in the emitter needs to know what a recursive class is.
    /// </summary>
    private (Slot Slot, IrClassType Type, bool ThenIsNull)? NullTest(IrExpr cond)
    {
        if (cond is not IrBinary { Op: BinOp.Eq or BinOp.Ne } b) return null;
        var tested = b.Left is IrNull ? b.Right : b.Right is IrNull ? b.Left : null;
        if (tested is not IrVar v || !_slots.TryGetValue(v.Name, out var slot)) return null;
        if (slot.Kind is not SlotKind.Object || slot.Type is not IrClassType { Nullable: true } k) return null;
        if (classes is null || !classes.TryGetValue(k.Name, out var decl) || decl.Recursion is null)
            return null;
        return (slot, k, b.Op is BinOp.Eq);
    }

    /// <summary>
    /// R10.7. The whole of §10's proof placement, and the reason the user writes no ghost
    /// code: the <c>if (n == null)</c> they had to write anyway <em>is</em> the case split
    /// on the model. <c>cases</c> connects the two before the test; the null branch learns
    /// the model is empty; the other branch opens the head cell, runs, and closes it again.
    ///
    /// <para>It is the same bracket R4.10 puts around a receiver, at a different place —
    /// around the branch a null test already delimits rather than around a whole body — and
    /// the field access inside it is the same rule, because the slot is rebound to the
    /// non-null reference for exactly the extent of the branch.</para>
    /// </summary>
    private void NullWindow(
        (Slot Slot, IrClassType Type, bool ThenIsNull) window, IrIf i,
        Action<IrStmt?> branch, bool tail)
    {
        var (slot, klass, thenIsNull) = window;
        var mod = Names.ClassModule(klass.Name);
        var opt = slot.Binder;
        var nullBranch = thenIsNull ? i.Then : i.Else;
        var consBranch = thenIsNull ? i.Else : i.Then;

        Line($"{mod}.{Names.ClassCases(klass.Name)} {opt};");
        Line($"if (B.is_null {opt}) {{");
        _indent++;
        // R10.4b. Preserving or consuming, read off the contract: a method that gave the
        // object away (R4.9c) owes nothing back, and leaving the empty invariant behind
        // would be a leftover resource.
        var nil = slot.Consumed ? Names.ClassElimNil(klass.Name) : Names.ClassNilCase(klass.Name);
        Line($"{mod}.{nil} {opt};");
        branch(nullBranch);
        if (!tail) Line("()");
        _indent--;
        Line("} else {");
        _indent++;
        Line($"{mod}.{Names.ClassElimCons(klass.Name)} {opt};");

        // Inside the window the reference is known non-null, so every rule that reaches a
        // field through a box applies unchanged — the slot names the box rather than the
        // option, and R3.8's read and R3.12's write need no case for recursion.
        var saved = _slots[slot.Name];
        _slots[slot.Name] = saved with { Window = true };
        _windows.Add($"{mod}.{Names.ClassIntroCons(klass.Name)} {opt};");
        try
        {
            branch(consBranch);
            if (!tail)
            {
                Line(_windows[^1]);
                Line("()");
            }
        }
        finally
        {
            _windows.RemoveAt(_windows.Count - 1);
            _slots[slot.Name] = saved;
        }
        _indent--;
        Line(tail ? "}" : "}");
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

        // R5.8c. A loop invariant is assembled by exactly the test R12.2 applies to a
        // contract: an `SlProp` clause is a resource and goes next to the `pts_to`s,
        // anything else is a proposition and goes inside the one `pure`. Without this a
        // loop could only ever state facts about values, so a loop that *walks* a data
        // structure — a cursor — has nowhere to say which part of it the invariant owns,
        // and every iterative traversal stays out of reach.
        foreach (var i in w.Invariants)
        {
            if (i.Type is IrPrim { Kind: PrimKind.SlProp })
                resources.Add(spec.Emit(i, scope).Text);
            else
                pure.Add(spec.AsProp(spec.Emit(i, scope)));
        }
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

        // R5.8d. The last statement of a loop body is in *tail position*, exactly as the
        // last statement of a method body is (R4.2). It matters for the same reason: a
        // Pulse `let mut` needs a postcondition at the end of its scope, and it has one
        // only where the scope ends at a construct that carries an annotation. A field read
        // inside the non-null branch of a test — which is what §12 asks every cursor loop to
        // write — is therefore typable in tail position and untypable one statement short of
        // it. Emitting the branch as a tail rather than terminating it with `()` is what
        // closes that gap, and it is the same rule the method case already applies.
        if (w.Step.IsEmpty && brkCell is null && contCell is null)
        {
            UnitTail(w.Body, plan);
            _indent--;
            Line("};");
            _escape = outerEscape;
            return;
        }

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

    /// <summary>
    /// R5.8d. A statement in tail position whose value is unit — the last statement of a
    /// loop body. It is <see cref="Tail"/> without the return value or the object epilogue,
    /// and it recurses through blocks and two-armed <c>if</c>s so that a nest of them is a
    /// nest of tails; anything else is an ordinary statement and keeps its <c>()</c>.
    ///
    /// <para>A null test that opens a §10 window is deliberately *not* treated as a tail:
    /// the window's closing lemma is emitted by the non-tail path, and moving it would be a
    /// change to R10.7 rather than to where a block ends.</para>
    /// </summary>
    private void UnitTail(IrStmt stmt, MethodPlan plan)
    {
        switch (stmt)
        {
            case IrBlock { Statements.IsEmpty: true }:
                Line("()");
                return;

            case IrBlock b:
                Scoped(() =>
                {
                    Sequence(b.Statements.RemoveAt(b.Statements.Length - 1), plan);
                    UnitTail(b.Statements[^1], plan);
                }, dropAtEnd: false);
                return;

            case IrIf { Else: not null } i when NullTest(i.Cond) is null:
            {
                if (i.Cond is IrBinary pnb && PlainNullTest(pnb) is { } ptest)
                {
                    PlainNullWindow(ptest, i, branch => UnitTail(branch!, plan), tail: true);
                    return;
                }
                var cond = Expr(i.Cond);
                Line($"if ({cond}) {{");
                _indent++;
                UnitTail(i.Then, plan);
                _indent--;
                Line("} else {");
                _indent++;
                UnitTail(i.Else, plan);
                _indent--;
                Line("}");
                return;
            }

            default:
                Statement(stmt, plan);
                Line("()");
                return;
        }
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

        // R17.6. The end of a borrow, before the naming bracket for the same reason a
        // `Share` is: the bracket names every owned resource at the slot it was declared
        // with, and `Pal.Restore` is the statement that stops the span being one.
        if (g.Kind is GhostKind.Restore) { Restore(g); return; }

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
                Line(Antiquotation.Expand(g.Text!, scope, Binder) + ";");
                return;
            case GhostKind.LemmaCall when g.Prop is IrCall call:
                // R14.5. A generic [Lemma] is applied to its type arguments first.
                Line($"{Names.SpecModule(call.Callee)}.{Names.Lemma(call.Callee)} " +
                     string.Join(" ", call.TypeArguments.Select(Types.Render)
                         .Concat(call.Args.Select((a, i) =>
                             SpecArgument(a, SpecEmitter.ParamType(call, i), scope)))) + ";");
                return;
            default:
                return;
        }
    }

    /// <summary>
    /// R17.6. <c>Pal.Restore(w)</c>: the ghost statement that gives a borrowed span back.
    /// </summary>
    /// <remarks>
    /// Which of the three library operations this is depends on where the span came from,
    /// which the slot recorded at the declaration that borrowed it. Nothing is inferred
    /// here, and nothing needs to be: the receipt is a resource, so the array, the
    /// permission, the bounds and both contents are recovered by unifying it against what
    /// the context holds (SliceFacts S8). That is what lets `Pal.Restore` take one argument.
    ///
    /// After this the span's slot is dropped. A later use of the name is then out of scope,
    /// which is the right message: what makes it unusable is that its ownership has gone.
    /// </remarks>
    private void Restore(IrGhostStmt g)
    {
        if (g.Prop is not IrVar v || Lookup(v.Name) is not { Kind: SlotKind.Span } slot)
        {
            diagnostics.SpanWindow(g.Loc, "`Pal.Restore` of anything but a borrowed span local");
            return;
        }

        if (slot.Origin is not { } origin)
        {
            diagnostics.SpanWindow(g.Loc,
                $"`Pal.Restore` of the span parameter `{v.Name}`, which this method did not borrow");
            return;
        }

        Line($"Span.{origin switch
        {
            SpanOrigin.Array => "restore_array",
            SpanOrigin.ArrayRange => "restore_array_range",
            _ => "restore_sub",
        }} {slot.Binder};");

        _slots.Remove(v.Name);
    }

    /// <summary>
    /// R17.5. Emits a borrow, binding the window to <paramref name="target"/>. One
    /// operation per origin, each consuming the source's ownership and producing a receipt.
    /// </summary>
    private string Borrow(IrSpanCreate create, string target)
    {
        var source = Expr(create.Source);
        if (create.Origin is SpanOrigin.Array)
        {
            Line($"let {target} = Span.of_array {source};");
            return target;
        }
        var start = Expr(create.Start!);
        var count = Expr(create.Length!);
        var op = create.Origin is SpanOrigin.ArrayRange ? "of_array_range" : "sub";
        Line($"let {target} = Span.{op} {source} {start} {count};");
        return target;
    }

    /// <summary>R17.1. Whether an expression denotes a span rather than an array.</summary>
    private bool IsSpan(IrExpr e) =>
        e.Type is IrSpanType ||
        (e is IrVar v && Lookup(v.Name) is { Type: IrSpanType });

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
    /// The object a Pulse binder stands for, if any. A conversion (R9.15) produces a
    /// reference with no C# name at all, so the binder — not the source name — is what
    /// identifies it once it has been emitted.
    /// </summary>
    private Slot? SlotByBinder(string binder) =>
        _objectLocals.FirstOrDefault(l => l.Binder == binder)
        ?? _slots.Values.FirstOrDefault(l => l.Kind == SlotKind.Object && l.Binder == binder);

    /// <summary>
    /// R4.7: a lemma is applied to the values the program holds, so its arguments are
    /// passed with their program types and receive no <c>Int32.v</c> coercion.
    /// </summary>
    /// <summary>
    /// R4.13. A lemma called from code takes its arguments under exactly the rule a lemma
    /// mentioned in a specification does: a machine value entering a mathematical
    /// parameter is C#'s implicit conversion, and is the `.v` of §6.
    /// </summary>
    private string SpecArgument(IrExpr arg, IrType? paramType, SpecScope scope) =>
        spec.Argument(arg, paramType, scope);

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

            // R4.9c, R4.12b. The call took this reference's invariant with it.
            case IrVar v when _slots.TryGetValue(v.Name, out var given) && given.Given is { } to:
                diagnostics.Error("PALCS0550", v.Loc,
                    $"`{v.Name}` cannot be used after it is passed to `{to}`, which takes " +
                    "ownership of it (R4.9c). What `" + v.Name + "` owned is now part of " +
                    "what that call produced: use the result instead.");
                return "()";

            // R9.16. The cast moved this reference's invariant onto the derived name.
            case IrVar v when _slots.TryGetValue(v.Name, out var cast) && cast.Cast is { } to:
                diagnostics.Error("PALCS0548", v.Loc,
                    $"`{v.Name}` cannot be used after it is cast to `{to}`. The cast moved " +
                    $"what `{v.Name}` owned onto the `{to}` reference (R9.16), which is the " +
                    "same object: use that name instead.");
                return "()";

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

            // R3.3/R17.3. `a.Length` and `s.Length`. One node, two libraries: a span's
            // length is `Slice.len`, which is pure and non-ghost exactly as an array's
            // header field is, so nothing but the qualifier differs.
            case IrLength len:
            {
                var array = Expr(len.Array);
                var t = Fresh();
                Line($"let {t} = {(IsSpan(len.Array) ? "Span." : "")}length_i32 {array};");
                return t;
            }

            // R6.4/R17.4. `a[i]` and `s[i]`, with the same bounds obligations.
            case IrElement el:
            {
                var array = Expr(el.Array);
                var index = Expr(el.Index);
                var t = Fresh();
                Line($"let {t} = {(IsSpan(el.Array) ? "Span." : "")}read {array} {index};");
                return t;
            }

            // R17.5. Borrowing. Each of the three forms consumes the source's ownership and
            // produces the window's, plus a receipt that only `Pal.Restore` can redeem.
            case IrSpanCreate create:
                return Borrow(create, Fresh());

            // R6.9. `new T[n]`. `Pulse.Lib.CSharp.Array.alloc` is where the garbage
            // collector is assumed: it carries no deallocation obligation, unlike
            // `Pulse.Lib.Array.alloc`, which is a stack allocation.
            // R10.2. `null` is the empty structure, and owning it is free — which is what
            // `intro_nil` says. Emitting the step here rather than at each position a null
            // may appear keeps `new Node(v, null)` and `x.next = null` the same rule.
            // R12.2. `null` on a `[Plain]` class is the null pointer and nothing else:
            // §12 derived no `intro_nil`, because it derived no predicate for the lemma to
            // be about. Whether a null pointer may stand where a segment is wanted is the
            // user's predicate's business.
            case IrNull pn when pn.Type is IrClassType pk
                && classes is not null && classes.TryGetValue(pk.Name, out var pnd) && pnd.IsPlain:
                return "B.null";

            // R15.8. `B.null` at a generic class says nothing about what it is empty *of*,
            // so the type argument `intro_nil` takes implicitly (R15.2) has nothing to
            // resolve against. Naming the empty structure first, at its type, is the
            // smallest thing that gives the implicit a source; the monomorphic case has
            // no ambiguity and so keeps the shorter form.
            case IrNull n when n.Type is IrClassType { TypeArguments.IsEmpty: false } gk:
            {
                var t = Fresh();
                Line($"let {t} : {Types.Render(gk with { Nullable = true })} = B.null;");
                Line($"{Names.ClassModule(gk.Name)}.{Names.ClassIntroNil(gk.Name)} {t} 1.0R;");
                return t;
            }

            case IrNull n when n.Type is IrClassType k:
                Line($"{Names.ClassModule(k.Name)}.{Names.ClassIntroNil(k.Name)} B.null 1.0R;");
                return "B.null";

            case IrNewArray na:
            {
                var length = Expr(na.Length);
                var t = Fresh();
                Line($"let {t} = alloc {length} {Default(na.Element)};");
                return t;
            }

            // R12.3. A field of a `[Plain]` reference. The same memory operation as R3.8 —
            // dereference the box, project the record — reached by a different slot kind,
            // because a plain reference carries no model and so is an ordinary value.
            case IrField { Receiver: IrVar pv } pf when
                _slots.TryGetValue(pv.Name, out var pobj)
                && pobj is { Kind: SlotKind.Value or SlotKind.Cell, Type: IrClassType pc }
                && classes is not null && classes.TryGetValue(pc.Name, out var pdecl)
                && pdecl.IsPlain:
            {
                if (!Reachable(pobj, pf.Loc, pf.Field)) return "()";
                // A cell slot holds the *reference*, so it is read first and the box is
                // projected out of what was read; a value slot already is the reference.
                var precv = pobj.Kind is SlotKind.Cell ? Expr(pv) : pobj.Binder;
                var pt = Fresh();
                Line($"let {pt} = B.op_Bang {precv};");
                return $"{pt}.{Names.ClassProjection(pc.Name, pf.Field)}";
            }

            // R3.8. A field of an object lives behind a box, so reading it is a memory
            // operation, not a projection: the object is dereferenced and the resulting
            // representation projected. Legal only between the opening `unfold` and the
            // closing `fold`, which is exactly where a method body lives.
            case IrField { Receiver: IrVar ov } f when
                _slots.TryGetValue(ov.Name, out var obj) && obj is { Kind: SlotKind.Object, Type: IrClassType oc }:
            {
                if (!Reachable(obj, f.Loc, f.Field)) return "()";
                var t = Fresh();
                Line($"let {t} = B.op_Bang {obj.NonNull};");
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

            // R12.4. Allocating a `[Plain]` object: build the record, box it. `B.alloc`
            // carries no deallocation obligation, which is the same assumption R6.9 makes
            // about `new T[n]` and for the same reason — C# has a collector.
            case IrAlloc al:
            {
                var box = Fresh();
                Line($"let {box} = B.alloc {AllocRecord(al)};");
                // R10.6b, again: `new` is non-null, and the proof of it is a library call.
                Line($"B.pts_to_not_null {box};");
                return box;
            }

            case IrNew n:
            {
                var fields = n.Fields.Select((f, i) =>
                    (i == 0 ? Names.Projection(n.Struct, f.Field) : Names.Field(f.Field))
                    + " = " + Expr(f.Value)).ToImmutableArray();
                // Parenthesised: in statement position Pulse reads a bare `{ … }` as a block.
                return "({ " + string.Join("; ", fields) + " })";
            }

            case IrUnary u:
                return Unary(u);
            // R12.3. A null test on a `[Plain]` reference in value position is the
            // representation's own question and nothing more: is the pointer null?
            case IrBinary { Op: BinOp.Eq or BinOp.Ne } pb when PlainNullTest(pb) is { } pt:
            {
                var t = Expr(pt.Tested);
                var name = Fresh();
                Line(pb.Op is BinOp.Eq
                    ? $"let {name} = B.is_null {t};"
                    : $"let {name} = not (B.is_null {t});");
                return name;
            }

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

            // R13.3. Run the effect where it stands, then yield the value. Emitting the
            // prelude through the ordinary statement path is what makes the effect land
            // in the right place: inside a loop guard it is re-run every iteration, and
            // inside a captured short-circuit branch it is run only when that branch is.
            case IrStmtExpr se:
                foreach (var s in se.Prelude) Statement(s, _plan!);
                return Expr(se.Value);

            default:
                diagnostics.Unsupported(expr.Loc, $"`{expr.GetType().Name}` in executable code");
                return "()";
        }
    }

    /// <summary>Emits a call, binding its result to <paramref name="binder"/>.</summary>
    private string Call(IrCall call, string binder)
    {
        var declared = PulseEmitter.DispatchOwner(classes, slots, call.Callee);
        var owner = PulseEmitter.DispatchClass(classes, slots, call);

        // R9.16. An indexed reference is owned through `class_C__inv_at`, and that is what
        // a dispatching wrapper's `_at` form asks for; anything else — a base-typed
        // parameter of an ordinary method, an argument passed as data — asks for the plain
        // invariant, so the index is dropped here, where it is in the way.
        // The arguments are computed first, because one of them may *be* a conversion
        // (R9.15) and the reference it produces is what the index has to be read off.
        var raw = call.Args.Select(Expr).ToImmutableArray();

        // R10.2b, at an argument. Under R10.2 the reference itself needs no coercion, but
        // its *invariant* is still stated through R10.3a's abbreviation, so `Inject` is
        // called here for the same reason it is at a return (R4.13) and at a field write
        // (R10.4). It returns the text unchanged; what it may emit is the rewrite.
        var args = raw
            .Select((text, i) => Inject(
                i < call.ParamTypes.Length ? call.ParamTypes[i] : null, call.Args[i], text))
            .ToImmutableArray();

        var indexed = false;
        for (var i = 0; i < raw.Length; i++)
        {
            if (SlotByBinder(raw[i]) is not { Index: not null } ix) continue;
            if (i == 0 && call.HasReceiver && owner is not null) { indexed = true; continue; }
            Forget(ix);
        }

        // R4.9c, R4.12b, on the calling side. A parameter the callee consumes takes the
        // argument's invariant with it, so the caller stops owning it here — it must not be
        // folded back at the end of the block (R4.14) and must not be handed to anything
        // else. C# would leave the name usable, so PALCS0550 says so at the next use rather
        // than leaving Pulse to fail on a resource that moved several statements earlier.
        Moved(call, raw);
        // R9.12. A call resolved to an `abstract` declaration is a virtual call: it goes
        // to the dispatching wrapper, which recovers the object and runs its vtable slot.
        // Nothing else about the call changes — the arguments, the implicit model binder
        // and the permission are found by the same rules as for a direct call, because
        // R9.9 gives the wrapper the same contract shape a direct method has.
        // R9.18. The wrapper's class is the receiver's static one; the member's name is
        // the one the class that declared it gave it, all the way down.
        var member = declared is null ? "" : Names.Member(call.Callee, declared);
        var callee = owner is not null
            ? indexed
                ? Names.DispatchAt(owner, member)
                : Names.Dispatch(owner, member)
            : Names.Function(call.Callee);

        // R9.7, on the calling side. An `override`'s contract is written at the model of
        // the class that declared the method, so its receiver is owned through
        // `class_C__as_B` — C's own invariant read at B's model — and not through
        // `class_C__inv`. A caller naming the override directly, which is what a call at
        // the leaf's own static type is, therefore has to hand the receiver over the same
        // way. The bracket is R9.14's view, opened and closed around one call; it is the
        // same two ghost steps R9.15's conversion emits, for the same reason, and it is
        // not a proof step but the rendering of "this reference is being used as a B".
        var view = Bracket(owner is null ? call : null, raw);

        // R14.5. Type arguments apply first, positionally, in declaration order. A generic
        // method with no value parameters still applies them, so the `()` below is reached
        // only by a call that is nullary in both senses.
        var tyArgs = call.TypeArguments.Select(Types.Render).ToImmutableArray();
        var applied = args.Length == 0 && tyArgs.Length == 0
            ? "()"
            : string.Join(" ", tyArgs.Concat(args));

        Line($"let {binder} = {callee} {applied};");
        Close(view);
        // R10.6c. The binder a call produced an object under is the name the context holds
        // that object's invariant under, exactly as for a `new` (R10.2b) or a parameter
        // (R10.6b). Recording it here is what stops R4.13 from re-binding it on the way
        // out of a method that hands back what it called: `let t' = t;` is not a rule of
        // the translation, and the frame rule cannot see through it.
        if (call.ResultType is IrClassType rk && !(classes?.TryGetValue(rk.Name, out var rc) == true && rc.IsPlain))
            _objectResults.Add(binder);
        return binder;
    }

    /// <summary>
    /// R4.9c, R4.12b. Records that a call took ownership of its consumed arguments.
    /// </summary>
    private void Moved(IrCall call, ImmutableArray<string> args)
    {
        if (consumed is null || !consumed.TryGetValue(call.Callee, out var positions)) return;
        for (var i = 0; i < args.Length; i++)
        {
            if (!positions.Contains(i)) continue;
            if (SlotByBinder(args[i]) is not { Kind: SlotKind.Object } obj) continue;
            _slots[obj.Name] = obj with { Kind = SlotKind.Value, Index = null, Given = call.Callee };
            _objectLocals.RemoveAll(l => l.Binder == obj.Binder);
        }
    }

    /// <summary>
    /// R9.7. Presents a direct call's receiver at the base model its <c>override</c>'s
    /// contract is written at, and reports what has to be closed afterwards.
    /// </summary>
    private (Slot Slot, string Class, string Base)? Bracket(IrCall? call, ImmutableArray<string> args)
    {
        if (call is null || !call.HasReceiver || args.Length == 0) return null;
        if (overrides is null || !overrides.TryGetValue(call.Callee, out var b)) return null;
        if (SlotByBinder(args[0]) is not { } recv) return null;
        // The method's own receiver is already open (R4.10) and already viewed at its base
        // by the signature, so a call on `this` needs neither half of the bracket.
        if (_objects.Any(o => o.Binder == recv.Binder)) return null;
        if (recv.Type is not IrClassType k) return null;

        var mod = Names.ClassModule(k.Name);
        var own = FreshValue(k.Name);
        Line($"with {own}. assert ({mod}.{Names.ClassInv(k.Name)} {recv.Binder} {recv.PermArg}{own});");

        // R9.15e, on a receiver that is never cast. The contract this call is checked
        // against is the base's (R9.7), so the same naming the cast needs is needed here:
        // a model left as an application of `forget` is only known at the derived class's
        // refinement (R9.5), and the base's own observations cannot be unfolded on it.
        var basis = FreshValue(b);
        Line($"let {basis} : erased ({Names.ClassModule(b)}.{Names.ClassModel(b)}) = " +
             $"hide ({mod}.{Names.ClassForget(k.Name)} {own});");
        Line($"fold ({mod}.{Names.ClassAsBase(k.Name, b)} {recv.Binder} " +
             $"{recv.PermArg}(reveal {basis}));");
        return (recv, k.Name, b);
    }

    /// <summary>Closes <see cref="Bracket"/>, at whatever model the call left behind.</summary>
    private void Close((Slot Slot, string Class, string Base)? view)
    {
        if (view is not { } v) return;
        var mod = Names.ClassModule(v.Class);
        var model = FreshValue(v.Class);
        Line($"with {model}. assert ({mod}.{Names.ClassAsBase(v.Class, v.Base)} " +
             $"{v.Slot.Binder} {v.Slot.PermArg}{model});");
        Line($"unfold ({mod}.{Names.ClassAsBase(v.Class, v.Base)} " +
             $"{v.Slot.Binder} {v.Slot.PermArg}{model});");
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

        // R18.1. R6.4 reads an operator's implementation off its operand type, and this
        // defaulted to `Int32` for an operand that was not primitive at all. `a == b` on
        // two objects then emitted `I32.eq` applied to two boxes: not a translation, and
        // not caught until F* refused to typecheck a file the user never asked to read.
        if (b.Left.Type is not IrPrim && b.Left.Type is not null)
        {
            diagnostics.Error("PALCS0593", b.Loc,
                $"`{b.Op}` is applied to operands of type `{b.Left.Type}`, and R6.4 gives an " +
                "operator a meaning only at a primitive type (doc/translation.md R18.1). " +
                (b.Left.Type is IrClassType
                    ? "Comparing two references is object identity, which the scheme has no story " +
                      "for: `Box` has a decidable equality, but nothing relates it to the ownership " +
                      "discipline, and two equal references are not interchangeable in a context " +
                      "that owns one of them. Compare the objects' models instead."
                    : "Compare values the rules give an operator for."));
            return "()";
        }

        var module = Types.Module((b.Left.Type as IrPrim)?.Kind ?? PrimKind.Int);

        // R13.5. C# takes a shift distance as an `int` whatever the operand's width, but
        // every one of F*'s `shift_left`/`shift_right` takes a `UInt32.t` — including
        // `Int64`'s and `UInt8`'s. The distance is therefore converted rather than
        // rendered at the operand's type, which is what it would otherwise inherit.
        if (b.Op is BinOp.Shl or BinOp.Shr &&
            (b.Right.Type as IrPrim)?.Kind is { } shiftKind && shiftKind != PrimKind.UInt)
        {
            r = Types.CastFunction(shiftKind, PrimKind.UInt) is { } toU32
                ? $"({toU32} {r})"
                : r;
        }

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
        // R9.16. A cast between reference types is a statement, not an expression: it
        // moves a resource, and the name it moves it to is the one every later mention
        // has to use. Anywhere else it would silently be the identity.
        if (cv.Target is IrClassType target)
        {
            // R9.15's conversion has a value, so it is an expression like any other. R9.16's
            // does too, but it also binds the *model equation* the caller reasons with, and
            // that equation needs a name — so the downcast stays a local declaration.
            if (Ancestors((cv.Operand.Type as IrClassType)?.Name, target.Name) is not null)
                return UpcastExpr(cv, target);

            diagnostics.Error("PALCS0547", cv.Loc,
                $"A cast down to `{target.Name}` is emitted only as the initialiser of a " +
                $"local declaration (R9.16): write `{target.Name} x = …;` and use `x`.");
            return "()";
        }

        var operand = Expr(cv.Operand);
        var from = (cv.Operand.Type as IrPrim)?.Kind;
        var to = (cv.Target as IrPrim)?.Kind;
        if (from == to) return operand;

        // R13.1. A numeric width conversion is `FStar.Int.Cast`'s corresponding function.
        //
        // Note what is *not* here: a proof obligation. Everywhere else pal-csharp insists
        // arithmetic does not overflow, because C#'s wrapping `+` is almost always an
        // accident. A cast is the opposite — writing `(byte)v` is the programmer asking
        // for truncation, and C#'s unchecked context, which is the default, defines it to
        // truncate. `FStar.Int.Cast`'s narrowing functions are modular, so they mean the
        // same thing (F48). Demanding `0 <= v < 256` here would be the emitter inventing a
        // refusal for an operation the source language defines (§0 rule 3); a user who
        // wants exactness proves the range themselves and F49 hands it back.
        if (from is { } f && to is { } t)
        {
            // `ushort` and `char` are both `U16.t`, so the conversion between them is the
            // identity and there is no cast function to name.
            var fn = Types.CastFunction(f, t);
            if (fn is null && Types.Machine(f) == Types.Machine(t)) return operand;
            if (fn is not null) return $"({fn} {operand})";
        }

        diagnostics.Unsupported(cv.Loc, $"The conversion from `{from}` to `{to}`",
            "Only conversions between C#'s integer types are translated.");
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

/// <summary>PAL's <c>$(…)</c> and <c>$&amp;(…)</c> antiquotations, reused verbatim.</summary>
public static class Antiquotation
{
    /// <param name="binder">
    /// Resolves <c>$&amp;(x)</c>: the Pulse name of the thing <c>x</c> lives in, rather
    /// than <c>$(x)</c>'s value of it. A ghost lemma about an array or a reference needs
    /// the array or the reference; the value is the wrong argument and, for a lemma that
    /// relates the two, an unusable one.
    /// </param>
    public static string Expand(string text, SpecScope scope, Func<string, string?>? binder = null)
    {
        var sb = new StringBuilder();
        for (var i = 0; i < text.Length; i++)
        {
            if (text[i] != '$' || i + 1 >= text.Length)
            {
                sb.Append(text[i]);
                continue;
            }

            var cell = text[i + 1] == '&' && i + 2 < text.Length && text[i + 2] == '(';
            if (!cell && text[i + 1] != '(')
            {
                sb.Append(text[i]);
                continue;
            }

            var depth = 0;
            var start = i + (cell ? 3 : 2);
            var j = start;
            for (; j < text.Length; j++)
            {
                if (text[j] == '(') depth++;
                else if (text[j] == ')' && depth-- == 0) break;
            }

            var name = text[start..j].Trim();
            sb.Append(cell
                ? binder?.Invoke(name) ?? name
                : scope.TryGet(name, out var term) ? term.Text : name);
            i = j;
        }
        return sb.ToString();
    }
}
