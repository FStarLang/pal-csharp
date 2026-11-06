using System.Collections.Immutable;
using Pal.Compiler.Diagnostics;
using Pal.Compiler.Ir;

namespace Pal.Compiler.Passes;

/// <summary>
/// The well-formedness validator, PAL's <c>Check</c> pass. It runs over the whole IR
/// after <see cref="Normalize"/> and before <c>Emit</c>.
///
/// <para>The lowering passes already reject constructs outside the supported subset one
/// node at a time, and <c>Emit</c> rejects a few more. What neither can see are the
/// *cross-node* conditions — a declaration whose signature contradicts its kind, two
/// declarations that would land in the same module, a recursive definition with no
/// measure. Those are this pass's job.</para>
///
/// <para>The pass is deliberately a pure predicate over the IR: it reports and never
/// rewrites. That keeps it runnable twice (as PAL runs it), and keeps the property that
/// what <c>Emit</c> sees is exactly what <c>Normalize</c> produced.</para>
///
/// <para>Its purpose is the sentinel property: a translation that would produce Pulse the
/// user cannot make sense of must stop here, with a diagnostic that names the C# mistake,
/// rather than reach F* and surface as an inscrutable type error in generated code.</para>
/// </summary>
public static class Check
{
    public static IrProgram Run(IrProgram program, DiagnosticBag diagnostics)
    {
        CheckModuleNames(program, diagnostics);

        // R3.9a. A `[Spec]` struct is erased, so it is spec-only wherever it appears —
        // and unlike the built-in spec-only types that is a fact about the *program*, not
        // about the IR node, so the set has to be collected before anything is checked.
        var specOnlyStructs = program.Declarations
            .OfType<IrStruct>().Where(t => t.IsSpecOnly).Select(t => t.Name).ToImmutableHashSet();

        var methods = program.Declarations.OfType<IrMethod>()
            .GroupBy(m => m.Name).ToImmutableDictionary(g => g.Key, g => g.First());

        // R9.15. Which conversions have an image under the scheme is a fact about the
        // hierarchy, so the hierarchy has to be in hand before any body is checked.
        var bases = program.Declarations.OfType<IrClass>()
            .Where(c => c.BaseClass is not null)
            .ToImmutableDictionary(c => c.Name, c => c.BaseClass!);

        // R12.3c. R10.7's window exists to place §10's case lemmas, so its rule about where
        // a null test may appear is a rule about classes that *have* a derived invariant.
        // A `[Plain]` class has none, so a null test of one is an ordinary comparison and
        // may appear wherever C# allows — including a loop condition, which is where a
        // cursor's is and which no window could ever be the extent of.
        var plain = program.Declarations.OfType<IrClass>()
            .Where(c => c.IsPlain).Select(c => c.Name).ToImmutableHashSet();

        foreach (var decl in program.Declarations)
        {
            switch (decl)
            {
                case IrMethod m when m.IsLemma: CheckLemma(m, diagnostics); break;
                case IrMethod m: CheckMethod(m, specOnlyStructs, plain, diagnostics); break;
                case IrSpecFunction s: CheckSpecFunction(s, program, diagnostics); break;
            }

            if (decl is IrMethod { Body: not null } withBody)
                CheckConversions(withBody, methods, bases, diagnostics);
        }

        CheckCallCycles(program, diagnostics);

        return program;
    }

    /// <summary>
    /// R2.1 gives every declaration a module of its own, and a call is a reference to
    /// another module. A cycle among them is therefore a cycle among F* modules, which F*
    /// does not report as a program error at all: it reports an internal failure and asks
    /// for a bug report. R10.7's measure would not help even where the recursion is
    /// well-founded, because a measure is checked *within* a definition and there is no
    /// one definition here.
    ///
    /// <para>Self-recursion is the case the scheme does have an image for — it becomes
    /// <c>fn rec</c> / <c>let rec</c> in the single module — and it is handled where the
    /// measure is, so it is excluded here.</para>
    /// </summary>
    private static void CheckCallCycles(IrProgram program, DiagnosticBag diagnostics)
    {
        var callees = new Dictionary<string, ImmutableHashSet<string>>();
        var located = new Dictionary<string, IrDecl>();

        foreach (var decl in program.Declarations)
        {
            var (name, calls) = decl switch
            {
                IrMethod { Body: { } body } m => (m.Name, Statements(body)
                    .SelectMany(Expressions).SelectMany(Subexpressions).OfType<IrCall>()),
                IrSpecFunction s => (s.Name, Subexpressions(s.Body).OfType<IrCall>()),
                _ => (null, null),
            };
            if (name is null || calls is null) continue;

            located[name] = decl;
            callees[name] = calls
                .Where(c => c.Kind is CalleeKind.Method or CalleeKind.Spec)
                .Select(c => c.Callee).Where(c => c != name).ToImmutableHashSet();
        }

        // Report each cycle once, against whichever of its members comes first in the
        // program, so that a pair does not produce two messages saying the same thing.
        foreach (var name in callees.Keys.OrderBy(n => n, StringComparer.Ordinal))
        {
            if (Path(name, name, [], out var cycle) &&
                cycle[0] == cycle.OrderBy(n => n, StringComparer.Ordinal).First())
                diagnostics.Error("PALCS0579", located[name].Loc,
                    $"`{name}` is part of a cycle of calls — {string.Join(" → ", cycle)} → {cycle[0]} " +
                    "— and R2.1 puts each of them in a module of its own, so the cycle is a " +
                    "cycle among F* modules and has no translation. Only direct recursion has " +
                    "one (doc/translation.md R10.7, R5.9): inline one of these into the other, " +
                    "or route the shared part through a `[Spec]` function that calls nothing.");
        }

        bool Path(string from, string goal, ImmutableList<string> seen, out ImmutableList<string> cycle)
        {
            cycle = seen.Add(from);
            if (!callees.TryGetValue(from, out var next)) return false;
            foreach (var to in next.OrderBy(n => n, StringComparer.Ordinal))
            {
                if (to == goal) return true;
                if (cycle.Contains(to)) continue;
                if (Path(to, goal, cycle, out cycle)) return true;
                cycle = seen.Add(from);
            }
            return false;
        }
    }

    // -----------------------------------------------------------------------
    // Whole-program
    // -----------------------------------------------------------------------

    /// <summary>
    /// R2.1 gives every declaration a module name. Two declarations sharing one would
    /// silently overwrite each other's <c>.fst</c> file, and the surviving proof would
    /// look like a passing verification of both.
    /// </summary>
    private static void CheckModuleNames(IrProgram program, DiagnosticBag diagnostics)
    {
        var seen = new Dictionary<string, IrDecl>();
        foreach (var decl in program.Declarations)
        {
            var key = $"{decl.GetType().Name}:{decl.Name}";
            if (seen.TryGetValue(key, out var first))
                // R2.1 gives a constructor the name `_ctor` regardless of its signature, so
                // two constructors of one class collide and "rename one" is advice C# does
                // not allow anyone to take. Naming the real remedy is the difference
                // between a diagnostic and a riddle.
                diagnostics.Error("PALCS0501", decl.Loc,
                    $"`{decl.Name}` would be emitted twice into the same module; " +
                    $"the other declaration is at {first.Loc}. " +
                    (decl.Name.EndsWith("__ctor", StringComparison.Ordinal)
                        ? "A constructor's generated name does not carry its signature " +
                          "(doc/translation.md R2.1, R18.3), so a class may declare only one. " +
                          "Declare a single constructor taking every field's value."
                        : "Rename one, or move it to a differently named class."));
            else
                seen[key] = decl;
        }
    }

    // -----------------------------------------------------------------------
    // Executable methods
    // -----------------------------------------------------------------------

    private static void CheckMethod(
        IrMethod m, ImmutableHashSet<string> specOnlyStructs,
        ImmutableHashSet<string> plain, DiagnosticBag diagnostics)
    {
        // An executable method's signature is read with the *program* meaning of each
        // type (R4.2). A spec-only type has no program meaning, so it cannot appear.
        if (SpecOnly(m.ReturnType, specOnlyStructs) is { } badReturn)
            diagnostics.Error("PALCS0500", m.Loc,
                $"`{m.Name}` returns `{badReturn}`, which exists only in specifications. " +
                "Mark the method `[Spec]` to make it a specification function, " +
                "or return a program type.");

        foreach (var p in m.Parameters)
            if (!p.IsGhost && p.Type is not IrGhostType &&
                SpecOnly(p.Type, specOnlyStructs) is { } bad)
                diagnostics.Error("PALCS0500", p.Loc,
                    $"The parameter `{p.Name}` has type `{bad}`, which exists only in " +
                    "specifications. Wrap it as `Ghost<...>` to pass it as a ghost " +
                    "argument, or mark the whole method `[Spec]`.");

        CheckGhostOrder(m, diagnostics);

        // R9.9. An `abstract` method is a vtable slot: its contract is a *demand* on every
        // subclass rather than a claim about a body, so having no body is what it is for.
        if (m.Body is null && m.PulseBody is null && !m.Admit && !m.IsAbstract)
            diagnostics.Error("PALCS0502", m.Loc,
                $"`{m.Name}` has no body. Give it a C# body, supply Pulse with " +
                "`[PulseBody(\"...\")]`, or mark it `[Admit]`.");

        if (m.Body is not null && m.PulseBody is not null)
            diagnostics.Error("PALCS0503", m.Loc,
                $"`{m.Name}` has both a C# body and a `[PulseBody]`. " +
                "pal-csharp will not silently choose between two implementations.");

        if (m.Admit)
            diagnostics.Warning("PALCS0900", m.Loc,
                $"`{m.Name}` is `[Admit]`ed: its contract is assumed, not proved.");

        // R10.7's counterpart to R5.9. A self-recursive method becomes `fn rec`, and F2
        // applies to it just as it applies to a loop: without a `decreases` the definition
        // is divergent and cannot compose with its callers. There is no counted-`for`
        // analogue to fall back on here — the measure is a term over the model — so the
        // only two answers are the one the user wrote and a refusal.
        if (m.Body is not null && m.Decreases is null &&
            Statements(m.Body).SelectMany(Expressions).SelectMany(Subexpressions)
                .OfType<IrCall>()
                .Any(c => c.Kind == CalleeKind.Method && c.Callee == m.Name))
            diagnostics.Error("PALCS0568", m.Loc,
                $"`{m.Name}` calls itself, so it needs a termination measure: add " +
                "`[Decreases(\"…\")]` naming a term that gets smaller at every recursive " +
                "call — for a traversal of a recursive class, its model " +
                "(doc/translation.md R10.7). Without one the translation is divergent and " +
                "no caller can use it.");

        if (m.Body is not null) CheckBody(m.Body, plain, diagnostics);
    }

    private static void CheckLemma(IrMethod m, DiagnosticBag diagnostics)
    {
        // R4.7. A lemma is a proof, so it produces a `Lemma`, whose "value" is unit.
        if (m.ReturnType is not IrPrim { Kind: PrimKind.Void })
            diagnostics.Error("PALCS0504", m.Loc,
                $"The `[Lemma]` `{m.Name}` returns `{m.ReturnType}`. " +
                "A lemma must return `void`; state what it proves in `[Ensures]`.");

        if (m.Ensures.IsEmpty)
            diagnostics.Warning("PALCS0901", m.Loc,
                $"The `[Lemma]` `{m.Name}` has no `[Ensures]`, so calling it proves nothing.");

        if (m.Body is null && m.PulseBody is null && !m.Admit)
            diagnostics.Error("PALCS0502", m.Loc,
                $"The `[Lemma]` `{m.Name}` has no proof. Give it a C# body, supply " +
                "F* with `[PulseBody(\"...\")]`, or mark it `[Admit]`.");

        if (m.Admit)
            diagnostics.Warning("PALCS0900", m.Loc,
                $"The `[Lemma]` `{m.Name}` is `[Admit]`ed: it is assumed, not proved.");
    }

    /// <summary>
    /// Ghost parameters lower to implicit binders, which Pulse places ahead of the
    /// explicit ones. Requiring them last in C# keeps call sites able to omit them.
    /// </summary>
    private static void CheckGhostOrder(IrMethod m, DiagnosticBag diagnostics)
    {
        var seenGhost = false;
        foreach (var p in m.Parameters)
        {
            // R27.39. A lifted lambda's ghosts are explicit: its callback passes them.
            var ghost = (p.IsGhost || p.Type is IrGhostType) && !p.ExplicitGhost;
            if (ghost) seenGhost = true;
            else if (seenGhost)
                diagnostics.Error("PALCS0505", p.Loc,
                    $"The explicit parameter `{p.Name}` follows a ghost parameter. " +
                    "Ghost parameters must come last so that callers can omit them.");
        }
    }

    // -----------------------------------------------------------------------
    // Specification functions
    // -----------------------------------------------------------------------

    private static void CheckSpecFunction(
        IrSpecFunction s, IrProgram program, DiagnosticBag diagnostics)
    {
        if (s.IsRecursive && s.Decreases is null)
            diagnostics.Error("PALCS0506", s.Loc,
                $"The recursive `[Spec]` function `{s.Name}` needs a termination measure. " +
                "Add `Pal.Decreases(m)` to it. pal-csharp does not guess one.");

        if (!s.IsRecursive && MentionsSelf(s))
            diagnostics.Error("PALCS0507", s.Loc,
                $"`{s.Name}` refers to itself but is not marked `[Spec(Recursive = true)]`.");

        // A specification is a pure function of its arguments. Calling an executable
        // method from one would make the specification depend on the heap.
        var programMethods = program.Declarations
            .OfType<IrMethod>().Where(m => !m.IsLemma).Select(m => m.Name)
            .ToImmutableHashSet();

        foreach (var call in Subexpressions(s.Body).OfType<IrCall>())
            if (call.Kind == CalleeKind.Method && programMethods.Contains(call.Callee))
                diagnostics.Error("PALCS0508", call.Loc,
                    $"The `[Spec]` function `{s.Name}` calls the executable method " +
                    $"`{call.Callee}`. A specification must be a pure function of its " +
                    "arguments; mark the callee `[Spec]` too.");
    }

    private static bool MentionsSelf(IrSpecFunction s) =>
        Subexpressions(s.Body).OfType<IrCall>().Any(c => c.Callee == s.Name);

    // -----------------------------------------------------------------------
    // Bodies
    // -----------------------------------------------------------------------

    private static void CheckBody(IrStmt body, ImmutableHashSet<string> plain, DiagnosticBag diagnostics)
    {
        foreach (var stmt in Statements(body))
        {
            switch (stmt)
            {
                case IrFor f:
                    // Normalize (R5.7) rewrites every `for`; one surviving means the
                    // pipeline was run out of order.
                    diagnostics.Error("PALCS0509", f.Loc,
                        "Internal error: a `for` loop reached Check un-normalized.");
                    break;

                case IrSwitch sw:
                    // The same, for R5.14's `switch`.
                    diagnostics.Error("PALCS0509", sw.Loc,
                        "Internal error: a `switch` reached Check un-normalized.");
                    break;

                case IrGhostStmt { Kind: GhostKind.Assume } a:
                    diagnostics.Warning("PALCS0902", a.Loc,
                        "`Pal.Assume` is unsound: this proposition is taken on trust.");
                    break;

                // R10.7. A null test opens a window whose extent is a *branch*, so the
                // test has to be the condition of an `if`. Inside a `&&`, or assigned to a
                // `bool`, there is no branch for the window to be the extent of — and the
                // reference would then be tested in one place and used in another, with
                // nothing to carry the case analysis between them.
                case var s2 when NullTestOutOfPosition(s2, plain) is { } bad:
                    diagnostics.Error("PALCS0569", bad.Loc,
                        "A null test of a recursive class's reference has to be the whole " +
                        "condition of an `if`: it is what opens the window in which the " +
                        "reference's fields are reachable (doc/translation.md R10.7), and a " +
                        "window's extent is a branch. Write `if (x == null) { … } else { … }`.");
                    break;

                case IrTry t when Jumps(t) is { } jump:
                    diagnostics.Error("PALCS0614", jump.Loc,
                        $"A `{(jump is IrReturn ? "return" : jump is IrBreak ? "break" : "continue")}` " +
                        "that leaves a `try` block or a `catch` handler. A Pulse `try` is a " +
                        "statement whose only exits are falling off its end and raising, so a " +
                        "jump out of it has no image. Set a flag, and act on it after the " +
                        "`try` (doc/translation.md R19.4).");
                    break;

                case IrWhile { Decreases: null, Counted: null } w:
                    // Belt and braces: Normalize reports this too (PALCS0200), but a
                    // loop reaching Emit without a measure produces a `while` that
                    // cannot compose with its continuation (F2), which is far harder to
                    // read than this message.
                    diagnostics.Error("PALCS0510", w.Loc,
                        "This loop reached Check with no termination measure.");
                    break;
            }
        }
    }

    /// <summary>
    /// R9.15a. C# inserts a reference conversion silently wherever a derived reference
    /// meets a base-typed context; the scheme's image of one is a ghost fold, and it is
    /// implemented only at a local declaration. Everywhere else the conversion would be
    /// dropped, and the resource the generated Pulse holds would not be the one it asks
    /// for — an error reported against generated code, in terms of a fold the user never
    /// wrote. This reports it against the C# instead, per the sentinel property.
    /// </summary>
    private static void CheckConversions(
        IrMethod m, ImmutableDictionary<string, IrMethod> methods,
        ImmutableDictionary<string, string> bases, DiagnosticBag diagnostics)
    {
        foreach (var stmt in Statements(m.Body!))
        {
            switch (stmt)
            {
                case IrReturn { Value: { } v }:
                    Report(v, m.ReturnType, "returned");
                    break;
                case IrAssign a:
                    Report(a.Value, a.Target.Type, "assigned");
                    break;
            }

            foreach (var call in Expressions(stmt).SelectMany(Subexpressions).OfType<IrCall>())
            {
                if (call.Kind != CalleeKind.Method) continue;
                if (!methods.TryGetValue(call.Callee, out var callee)) continue;

                // An instance call's receiver is Args[0] and is not among the declared
                // parameters; it is never a conversion site, because C# resolved the
                // callee *from* the receiver's static type.
                var offset = call.HasReceiver ? 1 : 0;
                if (call.Args.Length - offset != callee.Parameters.Length) continue;
                for (var i = 0; i < callee.Parameters.Length; i++)
                    Report(call.Args[i + offset], callee.Parameters[i].Type,
                        $"passed to `{callee.Parameters[i].Name}`");
            }
        }

        void Report(IrExpr value, IrType? target, string position)
        {
            // The frontend records the conversion (R9.15) and the emitter has one rule per
            // edge, applied once per level (R9.18c), so what is left to refuse is a
            // conversion between classes the hierarchy does not relate at all.
            var from = (value.Type as IrClassType)?.Name;
            if (from is null || target is not IrClassType to || from == to.Name) return;
            for (var at = from; bases.TryGetValue(at, out var up); at = up)
                if (up == to.Name) return;

            diagnostics.Error("PALCS0546", value.Loc,
                $"A `{from}` cannot be {position} at type `{to.Name}`: R9.15 converts a " +
                $"reference to a base class, and `{to.Name}` is not one of `{from}`'s.");
        }
    }

    // -----------------------------------------------------------------------
    // Helpers
    // -----------------------------------------------------------------------

    /// <summary>The spec-only type in <paramref name="t"/>, or null if it is a program type.</summary>
    private static IrType? SpecOnly(IrType t, ImmutableHashSet<string> specOnlyStructs) => t switch
    {
        IrPrim p when p.IsSpecNumeric || p.Kind == PrimKind.SlProp => t,
        IrSeqType => t,
        IrNamedType n when specOnlyStructs.Contains(n.Name) => t,
        IrArrayType a => SpecOnly(a.Element, specOnlyStructs) is null ? null : t,
        IrSpanType a => SpecOnly(a.Element, specOnlyStructs) is null ? null : t,
        _ => null,
    };

    /// <summary>
    /// R19.4. A <c>return</c>, or a <c>break</c>/<c>continue</c> not inside a loop of its
    /// own, in a try's body or handlers: a jump out of the try.
    /// </summary>
    private static IrStmt? Jumps(IrTry t)
    {
        return t.Catches.Select(c => (IrStmt)c.Body).Prepend(t.Body)
            .Select(b => Find(b, false)).FirstOrDefault(j => j is not null);

        static IrStmt? Find(IrStmt s, bool inLoop) => s switch
        {
            IrReturn => s,
            IrBreak or IrContinue => inLoop ? null : s,
            IrBlock b => b.Statements.Select(x => Find(x, inLoop)).FirstOrDefault(j => j is not null),
            IrIf i => Find(i.Then, inLoop) ?? (i.Else is null ? null : Find(i.Else, inLoop)),
            IrWhile w => Find(w.Body, true),
            IrTry inner => inner.Catches.Select(c => (IrStmt)c.Body).Prepend(inner.Body)
                .Select(b => Find(b, inLoop)).FirstOrDefault(j => j is not null),
            _ => null,
        };
    }

    /// <summary>
    /// Every statement in a body, outermost first. Shared with the emitter, which needs
    /// the same traversal to decide what a loop does to its enclosing object (R5.12).
    /// </summary>
    internal static IEnumerable<IrStmt> Statements(IrStmt stmt)
    {
        yield return stmt;
        switch (stmt)
        {
            case IrBlock b:
                foreach (var s in b.Statements)
                    foreach (var r in Statements(s)) yield return r;
                break;
            case IrIf i:
                foreach (var r in Statements(i.Then)) yield return r;
                if (i.Else is not null)
                    foreach (var r in Statements(i.Else)) yield return r;
                break;
            case IrWhile w:
                foreach (var r in Statements(w.Body)) yield return r;
                foreach (var step in w.Step)
                    foreach (var r in Statements(step)) yield return r;
                break;
            case IrFor f:
                foreach (var s in f.Init.Concat(f.Step))
                    foreach (var r in Statements(s)) yield return r;
                foreach (var r in Statements(f.Body)) yield return r;
                break;
            case IrSwitch sw:
                foreach (var r in Statements(sw.Scrutinee)) yield return r;
                foreach (var s in sw.Sections.SelectMany(sec => sec.Statements))
                    foreach (var r in Statements(s)) yield return r;
                break;
            case IrTry t:
                foreach (var r in Statements(t.Body)) yield return r;
                foreach (var c in t.Catches)
                    foreach (var r in Statements(c.Body)) yield return r;
                break;
        }
    }

    /// <summary>
    /// R10.7. A comparison against <c>null</c> that is not the whole condition of an
    /// <c>if</c>, if this statement holds one. A <c>null</c> in a *value* position — an
    /// argument, an initialiser, the right-hand side of an assignment — is an ordinary
    /// empty reference and is not a test, so it is not looked at here.
    /// </summary>
    private static IrExpr? NullTestOutOfPosition(IrStmt stmt, ImmutableHashSet<string> plain)
    {
        var allowed = stmt is IrIf i && IsNullTest(i.Cond, plain) ? i.Cond : null;
        foreach (var held in Expressions(stmt))
        {
            if (ReferenceEquals(held, allowed)) continue;
            foreach (var sub in Subexpressions(held))
                if (IsNullTest(sub, plain)) return sub;
        }
        return null;
    }

    private static bool IsNullTest(IrExpr e, ImmutableHashSet<string> plain)
    {
        if (e is not IrBinary { Op: BinOp.Eq or BinOp.Ne } b) return false;
        var tested = b.Left is IrNull ? b.Right : b.Right is IrNull ? b.Left : null;
        if (tested?.Type is not IrClassType k) return false;
        return !plain.Contains(k.Name);
    }

    /// <summary>The expressions a statement holds directly, not counting its substatements.</summary>
    internal static IEnumerable<IrExpr> Expressions(IrStmt stmt) => stmt switch
    {
        IrLocalDecl d => d.Init is null ? [] : [d.Init],
        IrAssign a => [a.Target, a.Value],
        IrExprStmt e => [e.Expr],
        IrArrayOp c => c.Args,
        IrReturn r => r.Value is null ? [] : [r.Value],
        IrIf i => [i.Cond],
        IrWhile w => [w.Cond],
        IrGhostStmt g => g.Prop is null ? [] : [g.Prop],
        IrThrow t => t.Value is null ? [] : [t.Value],
        IrTry t => [.. t.Catches.Where(c => c.When is not null).Select(c => c.When!)],
        _ => [],
    };

    /// <summary>Every subexpression of an expression, outermost first.</summary>
    internal static IEnumerable<IrExpr> Subexpressions(IrExpr expr)
    {
        yield return expr;
        IEnumerable<IrExpr> kids = expr switch
        {
            IrUnary u => [u.Operand],
            IrBinary b => [b.Left, b.Right],
            IrConditional c => [c.Cond, c.Then, c.Else],
            IrElement e => [e.Array, e.Index],
            IrLength l => [l.Array],
            IrField f => [f.Receiver],
            IrNew n => [.. n.Fields.Select(f => f.Value)],
            IrRefArg r => [r.Operand],
            IrLambdaRef l => l.Captures,
            IrCall c => c.Args,
            IrConvert c => [c.Operand],
            IrStmtExpr se => [se.Value],
            IrRaise ra => [ra.Exception],
            IrOld o => [o.Operand],
            IrLive l => [l.Operand],
            IrQuantifier q => [q.Body],
            IrNewArray n => n.Source is { } src ? [n.Length, src] : [n.Length],
            IrArraySearch s => [s.Array, s.Item, s.Start, s.Count],
            IrArrayBinarySearch b => [b.Array, b.Start, b.Count, b.Item, b.Comparer],
            IrContents c => [c.Array],
            IrSeqOp s => s.Args,
            IrListOp l => l.Args,
            IrSpecOp o => o.Args,
            _ => [],
        };
        foreach (var kid in kids)
            foreach (var r in Subexpressions(kid)) yield return r;
    }
}
