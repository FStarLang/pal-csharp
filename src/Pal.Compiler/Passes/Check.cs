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

        foreach (var decl in program.Declarations)
        {
            switch (decl)
            {
                case IrMethod m when m.IsLemma: CheckLemma(m, diagnostics); break;
                case IrMethod m: CheckMethod(m, diagnostics); break;
                case IrSpecFunction s: CheckSpecFunction(s, program, diagnostics); break;
            }
        }

        return program;
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
                diagnostics.Error("PALCS0501", decl.Loc,
                    $"`{decl.Name}` would be emitted twice into the same module; " +
                    $"the other declaration is at {first.Loc}. " +
                    "Rename one, or move it to a differently named class.");
            else
                seen[key] = decl;
        }
    }

    // -----------------------------------------------------------------------
    // Executable methods
    // -----------------------------------------------------------------------

    private static void CheckMethod(IrMethod m, DiagnosticBag diagnostics)
    {
        // An executable method's signature is read with the *program* meaning of each
        // type (R4.2). A spec-only type has no program meaning, so it cannot appear.
        if (SpecOnly(m.ReturnType) is { } badReturn)
            diagnostics.Error("PALCS0500", m.Loc,
                $"`{m.Name}` returns `{badReturn}`, which exists only in specifications. " +
                "Mark the method `[Spec]` to make it a specification function, " +
                "or return a program type.");

        foreach (var p in m.Parameters)
            if (!p.IsGhost && p.Type is not IrGhostType && SpecOnly(p.Type) is { } bad)
                diagnostics.Error("PALCS0500", p.Loc,
                    $"The parameter `{p.Name}` has type `{bad}`, which exists only in " +
                    "specifications. Wrap it as `Ghost<...>` to pass it as a ghost " +
                    "argument, or mark the whole method `[Spec]`.");

        CheckGhostOrder(m, diagnostics);

        if (m.Body is null && m.PulseBody is null && !m.Admit)
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

        if (m.Body is not null) CheckBody(m.Body, diagnostics);
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
            var ghost = p.IsGhost || p.Type is IrGhostType;
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

        foreach (var call in Walk(s.Body).OfType<IrCall>())
            if (call.Kind == CalleeKind.Method && programMethods.Contains(call.Callee))
                diagnostics.Error("PALCS0508", call.Loc,
                    $"The `[Spec]` function `{s.Name}` calls the executable method " +
                    $"`{call.Callee}`. A specification must be a pure function of its " +
                    "arguments; mark the callee `[Spec]` too.");
    }

    private static bool MentionsSelf(IrSpecFunction s) =>
        Walk(s.Body).OfType<IrCall>().Any(c => c.Callee == s.Name);

    // -----------------------------------------------------------------------
    // Bodies
    // -----------------------------------------------------------------------

    private static void CheckBody(IrStmt body, DiagnosticBag diagnostics)
    {
        foreach (var stmt in Walk(body))
        {
            switch (stmt)
            {
                case IrFor f:
                    // Normalize (R5.7) rewrites every `for`; one surviving means the
                    // pipeline was run out of order.
                    diagnostics.Error("PALCS0509", f.Loc,
                        "Internal error: a `for` loop reached Check un-normalized.");
                    break;

                case IrGhostStmt { Kind: GhostKind.Assume } a:
                    diagnostics.Warning("PALCS0902", a.Loc,
                        "`Pal.Assume` is unsound: this proposition is taken on trust.");
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

    // -----------------------------------------------------------------------
    // Helpers
    // -----------------------------------------------------------------------

    /// <summary>The spec-only type in <paramref name="t"/>, or null if it is a program type.</summary>
    private static IrType? SpecOnly(IrType t) => t switch
    {
        IrPrim p when p.IsSpecNumeric || p.Kind == PrimKind.SlProp => t,
        IrSeqType => t,
        IrArrayType a => SpecOnly(a.Element) is null ? null : t,
        _ => null,
    };

    private static IEnumerable<IrStmt> Walk(IrStmt stmt)
    {
        yield return stmt;
        switch (stmt)
        {
            case IrBlock b:
                foreach (var s in b.Statements)
                    foreach (var r in Walk(s)) yield return r;
                break;
            case IrIf i:
                foreach (var r in Walk(i.Then)) yield return r;
                if (i.Else is not null)
                    foreach (var r in Walk(i.Else)) yield return r;
                break;
            case IrWhile w:
                foreach (var r in Walk(w.Body)) yield return r;
                break;
            case IrFor f:
                foreach (var s in f.Init.Concat(f.Step))
                    foreach (var r in Walk(s)) yield return r;
                foreach (var r in Walk(f.Body)) yield return r;
                break;
        }
    }

    private static IEnumerable<IrExpr> Walk(IrExpr expr)
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
            IrCall c => c.Args,
            IrConvert c => [c.Operand],
            IrOld o => [o.Operand],
            IrLive l => [l.Operand],
            IrQuantifier q => [q.Body],
            IrContents c => [c.Array],
            IrSeqOp s => s.Args,
            _ => [],
        };
        foreach (var kid in kids)
            foreach (var r in Walk(kid)) yield return r;
    }
}
