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
    private readonly StringBuilder _sb = new();
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

    private string Fresh() => "t" + _temp++;
    private string FreshValue(string name) => $"v{name}_{_ghost++}";

    private void Line(string text) => _sb.Append(new string(' ', _indent * 2)).Append(text).Append('\n');

    public string EmitBody(IrMethod method, MethodPlan plan)
    {
        foreach (var (name, slot) in plan.Slots) _slots[name] = slot;

        if (method is { IsConstructor: true, ReturnType: IrClassType built })
        {
            Construct(method, built);
            return _sb.ToString();
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

        // R4.10b. A loop inside the `unfold`/`fold` window is refused, not approximated.
        // Pulse needs the loop's invariant to name every resource the body touches, and
        // inside the window those are the *unfolded* ones — `B.pts_to this r` and one
        // `A.pts_to` per array field, with `r` and the contents existentially quantified —
        // while the user's `Pal.Invariant` clauses would have to be read against the
        // representation rather than the model. That is a sub-scheme, and it is not
        // written. Emitting the folded invariant instead, which is what the loop rule
        // would do unaided, produces Pulse that cannot verify and whose failure points at
        // generated code; refusing it here points at the loop.
        if (_objects.Length > 0 && method.Body is not null && HasLoop(method.Body))
        {
            diagnostics.Unsupported(method.Loc,
                $"A loop inside the instance method `{method.Name}`",
                "The object's invariant is open across the whole body, so the loop would " +
                "have to carry the representation rather than the model. Move the loop " +
                "into a static method taking the array, or out into the caller.");
            return _sb.ToString();
        }

        // The invariant is abstract to the caller, so the body cannot touch a field until
        // it is unfolded, and the matching `fold` on each exit path re-establishes it.
        foreach (var obj in _objects) Line(Unfold(obj) + ";");

        // R4.2: rebind assigned by-value parameters as cells.
        foreach (var (cell, source) in plan.Prologue) Line($"let mut {cell} = {source};");

        var statements = method.Body is IrBlock b ? b.Statements : [method.Body!];
        EmitSequence(statements, method, plan);
        return _sb.ToString();
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
                EmitSequence(b.Statements, method, plan);
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

    private static bool HasLoop(IrStmt stmt) => stmt switch
    {
        IrWhile or IrFor => true,
        IrBlock b => b.Statements.Any(HasLoop),
        IrIf i => HasLoop(i.Then) || (i.Else is not null && HasLoop(i.Else)),
        _ => false,
    };

    private bool IsObjectBinder(string text) =>
        _objectLocals.Any(l => l.Binder == text) || _objects.Any(o => o.Binder == text);

    private static string Inv(IrClassType c) =>
        $"{Names.ClassModule(c.Name)}.{Names.ClassInv(c.Name)}";

    private static string Unfold(Slot obj) =>
        $"unfold {Inv((IrClassType)obj.Type)} {obj.Binder} {obj.PreModel}";

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
    private void DropLocals(string? returned)
    {
        foreach (var local in _objectLocals)
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
            if (obj.PostModel == obj.PreModel)
            {
                Line($"fold {Inv(klass)} {obj.Binder} {obj.PreModel};");
                continue;
            }

            if (classes is null || !classes.TryGetValue(klass.Name, out var decl))
            {
                diagnostics.Unsupported(method.Loc,
                    $"Mutating an object of class `{klass.Name}` whose model is not in this translation unit");
                continue;
            }

            Line($"fold {Inv(klass)} {obj.Binder} {ModelWitness(decl, obj)};");
        }
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
            scope.Bind(field.Name, new Term(
                projection, MethodPlan.KindOf(field.Type), field.Type));
        }

        return MethodPlan.KindOf(decl.ModelType) == TermKind.Math
            ? spec.Math(decl.ModelBody, scope)
            : $"({spec.Emit(decl.ModelBody, scope).Text})";
    }

    // =======================================================================
    // Statements
    // =======================================================================

    private void Statement(IrStmt stmt, MethodPlan plan)
    {
        switch (stmt)
        {
            // R3.8. An object local binds a reference. C# can rebind it, but nothing in
            // the supported subset does, and binding it immutably is what lets it be
            // handed to a callee that consumes and returns its invariant.
            case IrLocalDecl { Type: IrClassType oc, Init: not null } d:
            {
                var binder = Names.Local(d.Name);

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
                Sequence(b.Statements, plan);
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
        var live = w.Live.Where(n => _slots.TryGetValue(n, out var s) && s.Owns)
            .Select(n => _slots[n]).ToImmutableArray();
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

        var toFix = live.Where(s => unassigned.Contains(s.Name)).ToImmutableArray();
        if (toFix.Length > 0)
        {
            Line($"with {string.Join(" ", toFix.Select(s => fixedNames[s.Name]))}. " +
                 $"assert ({string.Join(" ** ", toFix.Select(s => s.Resource(fixedNames[s.Name])))});");
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
        foreach (var line in guard.Lines) _sb.Append(line);
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

        var invariants = w.Invariants.Select(i => spec.AsProp(spec.Emit(i, scope))).ToImmutableArray();
        Line("invariant " + MethodPlan.Clause(resources.ToImmutable(), invariants, existentials.ToImmutable()));

        if (w.Decreases is not null)
        {
            var measure = spec.Math(w.Decreases, DerefScope());
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
        var owned = _slots.Values.Where(s => s.Owns).ToImmutableArray();
        var scope = new SpecScope(plan.PreScope) { Pre = plan.PreScope };

        if (owned.Length > 0)
        {
            var names = owned.ToDictionary(s => s.Name, s => FreshValue(s.Name));
            foreach (var slot in owned)
                scope.Bind(slot.Name, new Term(names[slot.Name], MethodPlan.KindOf(slot.Type), slot.Type));
            Line($"with {string.Join(" ", owned.Select(s => names[s.Name]))}. " +
                 $"assert ({string.Join(" ** ", owned.Select(s => s.Resource(names[s.Name])))});");
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
        Line($"let {binder} = {Names.Function(call.Callee)} " +
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

    private readonly record struct Captured(ImmutableArray<string> Lines, string Term);

    /// <summary>
    /// Emits into a scratch buffer, so that a sub-block's let-bindings can be placed
    /// inside the branch or guard they belong to rather than hoisted out of it —
    /// hoisting would change evaluation order.
    /// </summary>
    private Captured Capture(Func<string> emit)
    {
        var saved = _sb.Length;
        var term = emit();
        var text = _sb.ToString(saved, _sb.Length - saved);
        _sb.Length = saved;
        return new Captured(
            text.Length == 0 ? [] : [.. text.Split('\n', StringSplitOptions.RemoveEmptyEntries).Select(l => l + "\n")],
            term);
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
        foreach (var line in whenTrue.Lines) _sb.Append(line);
        Line(whenTrue.Term);
        _indent--;
        Line("} else {");
        _indent++;
        foreach (var line in whenFalse.Lines) _sb.Append(line);
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
