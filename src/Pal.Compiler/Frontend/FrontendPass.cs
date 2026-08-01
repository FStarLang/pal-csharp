using System.Collections.Immutable;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using Pal.Compiler.Diagnostics;
using Pal.Compiler.Ir;

namespace Pal.Compiler.Frontend;

/// <summary>
/// The Collect and Lower stages: walks the user's syntax with a semantic model,
/// harvests annotations, binds the string specifications, and produces the IR.
/// </summary>
public static class FrontendPass
{
    public static IrProgram Run(CSharpCompilation compilation, DiagnosticBag diagnostics)
    {
        var known = WellKnown.For(compilation);
        var candidates = Collect(compilation, known);
        var sites = BuildSpecSites(compilation, known, candidates);

        var bound = SpecBinder.Bind(ref compilation, sites, diagnostics);

        var declarations = ImmutableArray.CreateBuilder<IrDecl>();
        foreach (var candidate in candidates)
        {
            // The semantic model must be re-fetched: adding the shim trees produced a
            // new compilation, and models are not portable across compilations.
            var model = compilation.GetSemanticModel(candidate.Syntax.SyntaxTree);
            var decl = LowerDeclaration(candidate, model, known, bound, diagnostics);
            if (decl is not null) declarations.Add(decl);
        }

        foreach (var include in CollectIncludes(compilation, known))
            declarations.Add(include);

        return new IrProgram(declarations.ToImmutable());
    }

    // -----------------------------------------------------------------------
    // Collect
    // -----------------------------------------------------------------------

    private sealed record Candidate(
        MethodDeclarationSyntax Syntax,
        IMethodSymbol Symbol,
        CalleeKind Kind);

    private static ImmutableArray<Candidate> Collect(CSharpCompilation compilation, WellKnown known)
    {
        var result = ImmutableArray.CreateBuilder<Candidate>();
        foreach (var tree in compilation.SyntaxTrees)
        {
            var model = compilation.GetSemanticModel(tree);
            foreach (var method in tree.GetRoot().DescendantNodes().OfType<MethodDeclarationSyntax>())
            {
                if (model.GetDeclaredSymbol(method) is not { } symbol) continue;
                if (Declarations.KindOf(symbol, known) is not { } kind) continue;
                result.Add(new Candidate(method, symbol, kind));
            }
        }
        return result.ToImmutable();
    }

    private static IEnumerable<IrIncludePulse> CollectIncludes(Compilation compilation, WellKnown known)
    {
        foreach (var data in Declarations.All(compilation.Assembly, known.IncludePulseAttribute))
        {
            var module = Declarations.StringArgument(data, 0);
            var body = Declarations.StringArgument(data, 1);
            if (module is null || body is null) continue;
            yield return new IrIncludePulse(
                Locations.From(Declarations.ArgumentLocation(data)), module, body);
        }
    }

    // -----------------------------------------------------------------------
    // Spec sites
    // -----------------------------------------------------------------------

    private static ImmutableArray<SpecSite> BuildSpecSites(
        CSharpCompilation compilation, WellKnown known, ImmutableArray<Candidate> candidates)
    {
        // Every type declaring a [Spec] or [Lemma] is `using static`-imported so that a
        // specification can name those helpers exactly as the C# around it does.
        var helperTypes = candidates
            .Where(c => c.Kind is CalleeKind.Spec or CalleeKind.Lemma)
            .Select(c => c.Symbol.ContainingType)
            .Distinct(SymbolEqualityComparer.Default)
            .Cast<INamedTypeSymbol>()
            .Select(t => $"using static {t.ToDisplayString(SymbolDisplayFormat.FullyQualifiedFormat)};")
            .ToImmutableArray();

        var sites = ImmutableArray.CreateBuilder<SpecSite>();
        foreach (var candidate in candidates)
        {
            var usings = BuildUsings(candidate, helperTypes);
            foreach (var (attribute, index, wantsResult) in SpecAttributes(candidate.Symbol, known))
            {
                var text = Declarations.StringArgument(attribute);
                if (text is null) continue;
                sites.Add(new SpecSite(
                    Key: $"{candidate.Symbol.ContainingType.Name}_{candidate.Symbol.Name}_{index}",
                    Text: text,
                    Location: Declarations.ArgumentLocation(attribute),
                    Parameters: ShimParameters(candidate.Symbol, known, wantsResult),
                    Usings: usings));
            }
        }
        return sites.ToImmutable();
    }

    private static ImmutableArray<string> BuildUsings(
        Candidate candidate, ImmutableArray<string> helperTypes)
    {
        var fileUsings = candidate.Syntax.SyntaxTree.GetRoot()
            .DescendantNodes()
            .OfType<UsingDirectiveSyntax>()
            .Select(u => u.ToString())
            .ToImmutableArray();

        var own = $"using static {candidate.Symbol.ContainingType.ToDisplayString(SymbolDisplayFormat.FullyQualifiedFormat)};";

        // A specification string is written as if it were an expression inside the
        // annotated method, so the method's own namespace has to be in scope: without
        // it a sibling class can be named unqualified (it is imported by `using
        // static`) but not qualified, which is the more natural way to write it.
        var ns = candidate.Symbol.ContainingNamespace;
        var enclosing = ns is null || ns.IsGlobalNamespace
            ? ImmutableArray<string>.Empty
            : ImmutableArray.Create($"using {ns.ToDisplayString()};");

        return
        [
            .. fileUsings,
            .. enclosing,
            $"using {WellKnown.Namespace};",
            $"using static {WellKnown.Namespace}.Pal;",
            .. helperTypes.Contains(own) ? ImmutableArray<string>.Empty : [own],
            .. helperTypes,
        ];
    }

    /// <summary>The spec-bearing attributes of a method, in declaration order.</summary>
    private static IEnumerable<(AttributeData Attribute, int Index, bool WantsResult)> SpecAttributes(
        IMethodSymbol symbol, WellKnown known)
    {
        var index = 0;
        foreach (var a in symbol.GetAttributes())
        {
            var cls = a.AttributeClass;
            if (Same(cls, known.RequiresAttribute)) yield return (a, index++, false);
            else if (Same(cls, known.EnsuresAttribute)) yield return (a, index++, true);
            else if (Same(cls, known.PreservesAttribute)) yield return (a, index++, false);
            else if (Same(cls, known.PreservesValueAttribute)) yield return (a, index++, false);
            else if (Same(cls, known.DecreasesAttribute)) yield return (a, index++, false);
        }
    }

    private static bool Same(ISymbol? a, ISymbol b) => SymbolEqualityComparer.Default.Equals(a, b);

    /// <summary>
    /// The binders a specification is entitled to see: the method's parameters by value
    /// (a spec talks about values, not storage), ghost parameters unwrapped from
    /// <c>Ghost&lt;T&gt;</c>, and — in a postcondition — <c>Result</c>.
    /// </summary>
    private static ImmutableArray<SpecParam> ShimParameters(
        IMethodSymbol symbol, WellKnown known, bool wantsResult)
    {
        var result = ImmutableArray.CreateBuilder<SpecParam>();
        foreach (var p in symbol.Parameters)
        {
            var type = known.IsGhost(p.Type) ? ((INamedTypeSymbol)p.Type).TypeArguments[0] : p.Type;
            result.Add(new SpecParam(p.Name, type));
        }
        if (wantsResult && !symbol.ReturnsVoid)
            result.Add(new SpecParam(SpecBinder.ResultParameter, symbol.ReturnType));
        return result.ToImmutable();
    }

    // -----------------------------------------------------------------------
    // Lower
    // -----------------------------------------------------------------------

    private static IrDecl? LowerDeclaration(
        Candidate candidate,
        SemanticModel model,
        WellKnown known,
        ImmutableDictionary<string, BoundSpec> bound,
        DiagnosticBag diagnostics)
    {
        var symbol = candidate.Symbol;
        var loc = Locations.From(candidate.Syntax.Identifier);

        var specs = ReadSpecs(symbol, known, bound, diagnostics);
        var parameters = LowerParameters(symbol, known, diagnostics);

        if (candidate.Kind == CalleeKind.Spec)
            return LowerSpecFunction(candidate, model, known, diagnostics, loc, parameters, specs);

        var returnType = known.MapType(symbol.ReturnType);
        if (returnType is null)
        {
            diagnostics.Unsupported(loc, $"The return type `{symbol.ReturnType}`");
            return null;
        }

        var lowerer = new StmtLowerer(model, known, diagnostics);
        var body = LowerBody(candidate.Syntax, lowerer);

        // Body-level contracts (surface option A2) lead the body and are equivalent to
        // the attribute form; both produce the same IR.
        var (bodyRequires, bodyEnsures, trimmed) = ExtractBodyContracts(candidate.Syntax, model, known, lowerer);

        var pulseBody = Declarations.Find(symbol, known.PulseBodyAttribute) is { } pb
            ? Declarations.StringArgument(pb) : null;

        return new IrMethod(
            loc, Naming.Of(symbol), parameters, returnType,
            [.. specs.Requires, .. bodyRequires],
            [.. specs.Ensures, .. bodyEnsures],
            specs.Decreases,
            trimmed ?? body)
        {
            IsLemma = candidate.Kind == CalleeKind.Lemma,
            PulseBody = pulseBody,
            Admit = Declarations.Has(symbol, known.AdmitAttribute),
            Preserves = specs.Preserves,
        };
    }

    private static IrDecl? LowerSpecFunction(
        Candidate candidate, SemanticModel model, WellKnown known, DiagnosticBag diagnostics,
        IrLoc loc, ImmutableArray<IrParam> parameters, Specs specs)
    {
        var returnType = known.MapType(candidate.Symbol.ReturnType);
        if (returnType is null)
        {
            diagnostics.Unsupported(loc, $"The [Spec] return type `{candidate.Symbol.ReturnType}`");
            return null;
        }

        var bodyExpression = candidate.Syntax.ExpressionBody?.Expression
            ?? candidate.Syntax.Body?.Statements
                .OfType<ReturnStatementSyntax>().FirstOrDefault()?.Expression;

        if (bodyExpression is null)
        {
            diagnostics.Unsupported(loc, "A [Spec] method without an expression body",
                "Write it as `[Spec] static bool P(...) => ...;`.");
            return null;
        }

        var lowerer = new ExprLowerer(model, known, diagnostics, specPosition: true);
        var recursive = Declarations.Find(candidate.Symbol, known.SpecAttribute) is { } spec &&
            spec.NamedArguments.Any(n => n.Key == "Recursive" && n.Value.Value is true);

        return new IrSpecFunction(loc, Naming.Of(candidate.Symbol), parameters, returnType,
            specs.Requires, lowerer.Lower(bodyExpression))
        {
            IsRecursive = recursive,
            Decreases = specs.Decreases,
        };
    }

    private static IrStmt? LowerBody(MethodDeclarationSyntax syntax, StmtLowerer lowerer)
    {
        if (syntax.Body is { } block) return lowerer.Lower(block);
        if (syntax.ExpressionBody is { } arrow)
            return new IrReturn(Locations.From(arrow), lowerer.LowerSpec(arrow.Expression));
        return null;
    }

    private sealed record Specs(
        ImmutableArray<IrExpr> Requires,
        ImmutableArray<IrExpr> Ensures,
        ImmutableArray<IrExpr> Preserves,
        IrExpr? Decreases);

    private static Specs ReadSpecs(
        IMethodSymbol symbol, WellKnown known,
        ImmutableDictionary<string, BoundSpec> bound, DiagnosticBag diagnostics)
    {
        var requires = ImmutableArray.CreateBuilder<IrExpr>();
        var ensures = ImmutableArray.CreateBuilder<IrExpr>();
        var preserves = ImmutableArray.CreateBuilder<IrExpr>();
        IrExpr? decreases = null;

        foreach (var (attribute, index, _) in SpecAttributes(symbol, known))
        {
            var key = $"{symbol.ContainingType.Name}_{symbol.Name}_{index}";
            if (!bound.TryGetValue(key, out var spec)) continue;

            var lowerer = new ExprLowerer(spec.Model, known, diagnostics, specPosition: true);
            var expr = lowerer.Lower(spec.Expression);

            var cls = attribute.AttributeClass;
            if (Same(cls, known.RequiresAttribute)) requires.Add(expr);
            else if (Same(cls, known.EnsuresAttribute)) ensures.Add(expr);
            else if (Same(cls, known.PreservesAttribute) || Same(cls, known.PreservesValueAttribute))
                preserves.Add(expr);
            else if (Same(cls, known.DecreasesAttribute)) decreases = expr;
        }

        return new Specs(requires.ToImmutable(), ensures.ToImmutable(), preserves.ToImmutable(), decreases);
    }

    private static ImmutableArray<IrParam> LowerParameters(
        IMethodSymbol symbol, WellKnown known, DiagnosticBag diagnostics)
    {
        var result = ImmutableArray.CreateBuilder<IrParam>();
        foreach (var p in symbol.Parameters)
        {
            var loc = p.Locations.Length > 0 ? Locations.From(p.Locations[0]) : IrLoc.None;
            var isGhost = known.IsGhost(p.Type);
            var declared = isGhost ? ((INamedTypeSymbol)p.Type).TypeArguments[0] : p.Type;
            var type = known.MapType(declared);
            if (type is null)
            {
                diagnostics.Unsupported(loc, $"The parameter type `{p.Type}`");
                continue;
            }

            result.Add(new IrParam(loc, p.Name, type, Declarations.ModeOf(p))
            {
                IsGhost = isGhost,
                Consumes = Declarations.Has(p, known.ConsumesAttribute),
                Plain = Declarations.Has(p, known.PlainAttribute),
                Fraction = Declarations.Find(p, known.FracAttribute) is { } f
                    ? Declarations.StringArgument(f) : null,
            });
        }
        return result.ToImmutable();
    }

    /// <summary>
    /// Reads leading <c>Pal.Requires</c> / <c>Pal.Ensures</c> calls out of a method
    /// body. They are the typed alternative to the attribute form (surface option A2).
    /// </summary>
    private static (ImmutableArray<IrExpr> Requires, ImmutableArray<IrExpr> Ensures, IrStmt? Body)
        ExtractBodyContracts(
            MethodDeclarationSyntax syntax, SemanticModel model, WellKnown known, StmtLowerer lowerer)
    {
        if (syntax.Body is not { } block)
            return ([], [], null);

        var requires = ImmutableArray.CreateBuilder<IrExpr>();
        var ensures = ImmutableArray.CreateBuilder<IrExpr>();
        var leading = 0;

        foreach (var statement in block.Statements)
        {
            if (statement is not ExpressionStatementSyntax { Expression: InvocationExpressionSyntax call }) break;
            if (model.GetSymbolInfo(call).Symbol is not IMethodSymbol m || !known.IsPalIntrinsic(m)) break;

            if (m.Name == nameof(PalLang.Pal.Requires))
                requires.Add(lowerer.LowerSpec(call.ArgumentList.Arguments[0].Expression));
            else if (m.Name == nameof(PalLang.Pal.Ensures))
                ensures.Add(lowerer.LowerSpec(call.ArgumentList.Arguments[0].Expression));
            else break;

            leading++;
        }

        if (leading == 0) return ([], [], null);

        var body = new IrBlock(Locations.From(block),
            [.. block.Statements.Skip(leading).Select(lowerer.Lower)]);
        return (requires.ToImmutable(), ensures.ToImmutable(), body);
    }
}
