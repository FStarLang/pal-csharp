using System.Collections.Immutable;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using Pal.Compiler.Diagnostics;
using Pal.Compiler.Emit;
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
        var structs = CollectStructs(compilation, known, diagnostics);
        var classes = CollectClasses(compilation, known, diagnostics);
        ReportUncollected(compilation, known, classes, diagnostics);
        var sites = BuildSpecSites(compilation, known, candidates)
            .AddRange(BuildStructSpecSites(structs))
            .AddRange(BuildClassSpecSites(classes));

        var bound = SpecBinder.Bind(ref compilation, sites, diagnostics);

        var declarations = ImmutableArray.CreateBuilder<IrDecl>();
        foreach (var s in structs)
            declarations.Add(LowerStruct(s, known, bound, diagnostics));

        foreach (var c in classes)
            declarations.Add(LowerClass(
                c, known, bound, compilation.GetSemanticModel(c.Syntax.SyntaxTree), diagnostics));

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
        BaseMethodDeclarationSyntax Syntax,
        IMethodSymbol Symbol,
        CalleeKind Kind)
    {
        /// <summary>The name token: a method's identifier, or a constructor's type name.</summary>
        public SyntaxToken Identifier => Syntax switch
        {
            MethodDeclarationSyntax m => m.Identifier,
            ConstructorDeclarationSyntax c => c.Identifier,
            _ => Syntax.GetFirstToken(),
        };

        public ArrowExpressionClauseSyntax? ExpressionBody => Syntax switch
        {
            MethodDeclarationSyntax m => m.ExpressionBody,
            ConstructorDeclarationSyntax c => c.ExpressionBody,
            _ => null,
        };

    }

    private static ImmutableArray<Candidate> Collect(CSharpCompilation compilation, WellKnown known)
    {
        var result = ImmutableArray.CreateBuilder<Candidate>();
        foreach (var tree in compilation.SyntaxTrees)
        {
            var model = compilation.GetSemanticModel(tree);
            foreach (var method in tree.GetRoot().DescendantNodes().OfType<BaseMethodDeclarationSyntax>())
            {
                if (model.GetDeclaredSymbol(method) is not IMethodSymbol symbol) continue;
                if (Declarations.KindOf(symbol, known) is not { } kind) continue;
                result.Add(new Candidate(method, symbol, kind));
            }
        }
        return result.ToImmutable();
    }

    /// <summary>
    /// Refuse, rather than ignore, an annotated member the frontend cannot collect.
    /// </summary>
    /// <remarks>
    /// <see cref="Collect"/> keeps only static ordinary methods plus <c>[Spec]</c> and
    /// <c>[Lemma]</c> members, and used to drop everything else without a word. For an
    /// annotated member that silence is the worst possible outcome: `palcs` would report
    /// "0 error(s)", no module would be emitted, and nothing downstream would notice that
    /// a contract had simply evaporated. Classes are specified in translation.md §3.4 but
    /// not yet implemented, so until they are, saying so is the whole job.
    /// </remarks>
    private static void ReportUncollected(
        CSharpCompilation compilation, WellKnown known,
        ImmutableArray<ClassCandidate> classes, DiagnosticBag diagnostics)
    {
        var translated = classes
            .Select(c => (ISymbol)c.Symbol)
            .ToImmutableHashSet(SymbolEqualityComparer.Default);

        foreach (var tree in compilation.SyntaxTrees)
        {
            var model = compilation.GetSemanticModel(tree);
            foreach (var syntax in tree.GetRoot().DescendantNodes())
            {
                var symbol = syntax switch
                {
                    MethodDeclarationSyntax m => (ISymbol?)model.GetDeclaredSymbol(m),
                    ConstructorDeclarationSyntax c => model.GetDeclaredSymbol(c),
                    PropertyDeclarationSyntax p => model.GetDeclaredSymbol(p),
                    ClassDeclarationSyntax t => model.GetDeclaredSymbol(t),
                    _ => null,
                };
                if (symbol is null) continue;

                // A class whose own declaration carries [Invariant] or [Model], or an
                // annotated instance member of one: all of these are §3.4, not yet built.
                var isClassMember =
                    symbol is INamedTypeSymbol { TypeKind: TypeKind.Class }
                        ? Declarations.IsAnnotated(symbol, known)
                        : symbol is { IsStatic: false, ContainingType.TypeKind: TypeKind.Class }
                          && Declarations.IsAnnotated(symbol, known);
                if (!isClassMember) continue;

                // A class the frontend now translates, and its members, are not dropped.
                var owner = symbol as INamedTypeSymbol ?? symbol.ContainingType;
                if (owner is not null && translated.Contains(owner)) continue;

                // A [Spec]/[Lemma] member is collected on its own terms; only genuinely
                // dropped members are reported here.
                if (symbol is IMethodSymbol method && Declarations.KindOf(method, known) is not null)
                    continue;

                diagnostics.Error("PALCS0530",
                    Locations.From(syntax switch
                    {
                        MethodDeclarationSyntax m => m.Identifier.GetLocation(),
                        ConstructorDeclarationSyntax c => c.Identifier.GetLocation(),
                        PropertyDeclarationSyntax p => p.Identifier.GetLocation(),
                        ClassDeclarationSyntax t => t.Identifier.GetLocation(),
                        _ => syntax.GetLocation(),
                    }),
                    $"`{symbol.Name}` is an annotated class member, and pal-csharp does not translate " +
                    "classes yet. The scheme is specified in doc/translation.md §3.4 and §4.5. " +
                    "Until it is implemented, move the state into a struct passed by `ref`, with any " +
                    "array it describes passed alongside it rather than held inside it.");
            }
        }
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
    // Structs (R3.4)
    // -----------------------------------------------------------------------

    /// <summary>One field of a struct: a C# field, or an auto-property's storage.</summary>
    private sealed record StructField(ISymbol Symbol, string Name, ITypeSymbol Type, IrType Mapped);

    private sealed record StructCandidate(
        StructDeclarationSyntax Syntax,
        INamedTypeSymbol Symbol,
        ImmutableArray<StructField> Fields,
        ImmutableArray<string> Usings,
        bool IsSpecOnly);

    private static ImmutableArray<StructCandidate> CollectStructs(
        CSharpCompilation compilation, WellKnown known, DiagnosticBag diagnostics)
    {
        var result = ImmutableArray.CreateBuilder<StructCandidate>();
        foreach (var tree in compilation.SyntaxTrees)
        {
            var model = compilation.GetSemanticModel(tree);
            foreach (var syntax in tree.GetRoot().DescendantNodes().OfType<StructDeclarationSyntax>())
            {
                if (model.GetDeclaredSymbol(syntax) is not { } symbol) continue;
                if (Declarations.Has(symbol, known.PulseTypeAttribute)) continue;

                // R3.9a. `[Spec]` on a struct declares a *spec-only* type: it is erased,
                // it never appears in executable code, and so — unlike R3.4's ordinary
                // struct — its fields may be spec-only types. That is not a convenience:
                // R3.9 requires the model of a bounded container to be a product of its
                // contents and its capacity, and every built-in spec-only type is atomic,
                // so without this there is no way to write one at all.
                var specOnly = Declarations.Has(symbol, known.SpecAttribute);

                var loc = Locations.From(syntax.Identifier);
                var fields = ImmutableArray.CreateBuilder<StructField>();
                var ok = true;

                foreach (var member in symbol.GetMembers())
                {
                    var (name, type) = member switch
                    {
                        // An auto-property's backing field is nameless in C# and appears
                        // in `GetMembers` alongside the property; the property is the
                        // form the user wrote and the one specifications name.
                        IFieldSymbol { IsStatic: false, IsConst: false, AssociatedSymbol: null } f
                            => (f.Name, f.Type),
                        IPropertySymbol { IsStatic: false, IsIndexer: false } p
                            when p.GetMethod is not null && IsAuto(p) => (p.Name, p.Type),
                        _ => (null, null),
                    };
                    if (name is null || type is null) continue;

                    var mapped = known.MapType(type);
                    if (mapped is null || !(specOnly ? IsSpecField(mapped) : IsValueField(mapped)))
                    {
                        // R3.4: a field owning a resource would need the fold/unfold
                        // predicate discipline this rule exists to avoid.
                        diagnostics.Error("PALCS0511",
                            Locations.From(member.Locations.FirstOrDefault() ?? Location.None),
                            $"The field `{symbol.Name}.{name}` has type `{type}`, which a " +
                            (specOnly ? "spec-only struct" : "struct") + " cannot hold. " +
                            (specOnly
                                ? "A [Spec] struct is a ghost value, so its fields must be ghost: scalars, " +
                                  "`SpecInt`, `Seq<T>`, or other structs. It cannot own a resource."
                                : "A translated struct's fields must be values: scalars, or other translated " +
                                  "structs. Pass an array alongside the struct rather than inside it."));
                        ok = false;
                        continue;
                    }
                    fields.Add(new StructField(member, name, type, mapped));
                }

                if (!ok) continue;
                if (symbol.Name.Length == 0) continue;
                _ = loc;
                result.Add(new StructCandidate(
                    syntax, symbol, fields.ToImmutable(), BuildTypeUsings(syntax, symbol), specOnly));
            }
        }
        return result.ToImmutable();
    }

    private static bool IsAuto(IPropertySymbol p) =>
        p.ContainingType.GetMembers().OfType<IFieldSymbol>()
            .Any(f => SymbolEqualityComparer.Default.Equals(f.AssociatedSymbol, p));

    /// <summary>R3.4: the field types a struct may hold.</summary>
    private static bool IsValueField(IrType type) => type is IrPrim or IrNamedType;

    /// <summary>
    /// R3.9a: the field types a <c>[Spec]</c> struct may hold. Wider than R3.4 by exactly
    /// the spec-only types, and no wider: a ghost value still cannot own a resource, so an
    /// array or a class reference is refused here as it is there.
    /// </summary>
    private static bool IsSpecField(IrType type) => type is IrPrim or IrNamedType or IrSeqType;

    /// <summary>
    /// R3.4: a refinement is bound with the struct's fields in scope as simple names,
    /// so <c>[Refine("Lo &lt;= Hi")]</c> reads as it would inside an instance method.
    /// </summary>
    private static ImmutableArray<SpecSite> BuildStructSpecSites(
        ImmutableArray<StructCandidate> structs)
    {
        var sites = ImmutableArray.CreateBuilder<SpecSite>();
        foreach (var s in structs)
        {
            var parameters = s.Fields.Select(f => new SpecParam(f.Name, f.Type)).ToImmutableArray();
            var index = 0;
            foreach (var (text, location) in Refinements(s))
                sites.Add(new SpecSite(
                    Key: $"{s.Symbol.Name}_refine_{index++}",
                    Text: text,
                    Location: location,
                    Parameters: parameters,
                    Usings: s.Usings));
        }
        return sites.ToImmutable();
    }

    /// <summary>
    /// Every <c>[Refine]</c> on the struct and on its fields, in declaration order. Both
    /// forms mean the same thing and see the same binders, so they share one list: a
    /// field's refinement is simply one that happens to mention only that field.
    /// </summary>
    private static IEnumerable<(string Text, Location Location)> Refinements(StructCandidate s)
    {
        foreach (var data in s.Symbol.GetAttributes())
            if (IsRefine(data) && Declarations.StringArgument(data) is { } text)
                yield return (text, Declarations.ArgumentLocation(data));

        foreach (var field in s.Fields)
            foreach (var data in field.Symbol.GetAttributes())
                if (IsRefine(data) && Declarations.StringArgument(data) is { } text)
                    yield return (text, Declarations.ArgumentLocation(data));

        static bool IsRefine(AttributeData data) =>
            data.AttributeClass?.Name is "RefineAttribute" or "RefineAlwaysAttribute";
    }

    private static IrStruct LowerStruct(
        StructCandidate s,
        WellKnown known,
        ImmutableDictionary<string, BoundSpec> bound,
        DiagnosticBag diagnostics)
    {
        var fields = s.Fields
            .Select(f => new IrFieldDecl(
                Locations.From(f.Symbol.Locations.FirstOrDefault() ?? Location.None), f.Name, f.Mapped))
            .ToImmutableArray();

        var refinements = ImmutableArray.CreateBuilder<IrExpr>();
        for (var i = 0; i < Refinements(s).Count(); i++)
            if (bound.TryGetValue($"{s.Symbol.Name}_refine_{i}", out var spec))
                refinements.Add(new ExprLowerer(spec.Model, known, diagnostics, specPosition: true)
                    .Lower(spec.Expression));

        return new IrStruct(
            Locations.From(s.Syntax.Identifier), s.Symbol.Name, fields, refinements.ToImmutable())
        {
            IsSpecOnly = s.IsSpecOnly,
        };
    }

    private static ImmutableArray<string> BuildTypeUsings(
        StructDeclarationSyntax syntax, INamedTypeSymbol symbol)
    {
        var fileUsings = syntax.SyntaxTree.GetRoot()
            .DescendantNodes()
            .OfType<UsingDirectiveSyntax>()
            .Select(u => u.ToString())
            .ToImmutableArray();

        var ns = symbol.ContainingNamespace;
        var enclosing = ns is null || ns.IsGlobalNamespace
            ? ImmutableArray<string>.Empty
            : ImmutableArray.Create($"using {ns.ToDisplayString()};");

        return
        [
            .. fileUsings,
            .. enclosing,
            $"using {WellKnown.Namespace};",
            $"using static {WellKnown.Namespace}.Pal;",
        ];
    }


    // -----------------------------------------------------------------------
    // Classes (§3.4)
    // -----------------------------------------------------------------------

    /// <summary>A <c>[Spec]</c> member of a class: a pure function of the model (R3.9c).</summary>
    private sealed record ObservationMember(ISymbol Symbol, string Name, IrType ReturnType, ExpressionSyntax Body);

    private sealed record ClassCandidate(
        ClassDeclarationSyntax Syntax,
        INamedTypeSymbol Symbol,
        ImmutableArray<StructField> Fields,
        ISymbol ModelSymbol,
        IrType ModelType,
        ExpressionSyntax ModelBody,
        ImmutableArray<ObservationMember> Observations,
        ImmutableArray<string> Usings);

    /// <summary>
    /// Collects every annotated <c>sealed class</c>. A class is annotated when it carries
    /// a <c>[Model]</c> member, which R3.9 makes mandatory: without one there is nothing
    /// for the invariant to relate the representation to, and every method specification
    /// would collapse to memory safety.
    /// </summary>
    private static ImmutableArray<ClassCandidate> CollectClasses(
        CSharpCompilation compilation, WellKnown known, DiagnosticBag diagnostics)
    {
        var result = ImmutableArray.CreateBuilder<ClassCandidate>();
        foreach (var tree in compilation.SyntaxTrees)
        {
            var model = compilation.GetSemanticModel(tree);
            foreach (var syntax in tree.GetRoot().DescendantNodes().OfType<ClassDeclarationSyntax>())
            {
                if (model.GetDeclaredSymbol(syntax) is not { } symbol) continue;
                if (symbol.IsStatic) continue;

                var modelMembers = symbol.GetMembers()
                    .Where(m => Declarations.Has(m, known.ModelAttribute))
                    .ToImmutableArray();

                // A class with no [Model] and no annotation at all is an ordinary C#
                // class the translator has no business touching.
                if (modelMembers.Length == 0)
                {
                    // A specification on an instance member is just as much a request to
                    // translate the class as an [Invariant] is, and it is the likelier
                    // mistake: the user wrote the contract and forgot the model. Saying so
                    // here is much more useful than the PALCS0530 the member would
                    // otherwise draw, which reports the symptom rather than the cause.
                    var annotated = Declarations.Has(symbol, known.InvariantAttribute) ||
                        symbol.GetMembers().OfType<IMethodSymbol>()
                            .Any(m => !m.IsStatic && SpecAttributes(m, known).Any());

                    if (annotated)
                        diagnostics.Error("PALCS0524", Locations.From(syntax.Identifier),
                            $"`{symbol.Name}` is specified but declares no `[Model]` member. " +
                            "A class needs a model for its invariant and its contracts to relate the " +
                            "fields to; without one every method specification would say only that the " +
                            "object is well formed. Add a private `[Model]` member whose expression body " +
                            "is the abstraction function.");
                    continue;
                }

                if (modelMembers.Length > 1)
                {
                    diagnostics.Error("PALCS0524", Locations.From(syntax.Identifier),
                        $"`{symbol.Name}` declares {modelMembers.Length} `[Model]` members. " +
                        "A class has exactly one abstraction function, because its invariant relates " +
                        "the representation to exactly one model.");
                    continue;
                }

                // R4.13: a per-class invariant cannot express behavioural subtyping, so
                // M2 is sealed classes only.
                if (!symbol.IsSealed)
                {
                    diagnostics.Error("PALCS0521", Locations.From(syntax.Identifier),
                        $"`{symbol.Name}` is not `sealed`. pal-csharp translates sealed classes only: " +
                        "a per-class invariant cannot express what an overriding method would have to " +
                        "promise, so inheritance has no sound reading in the scheme.");
                    continue;
                }

                if (!TryCollectClass(syntax, symbol, modelMembers[0], known, diagnostics, out var candidate))
                    continue;
                result.Add(candidate);
            }
        }
        return result.ToImmutable();
    }

    private static bool TryCollectClass(
        ClassDeclarationSyntax syntax,
        INamedTypeSymbol symbol,
        ISymbol modelSymbol,
        WellKnown known,
        DiagnosticBag diagnostics,
        out ClassCandidate candidate)
    {
        candidate = null!;
        var ok = true;

        var fields = ImmutableArray.CreateBuilder<StructField>();
        var observations = ImmutableArray.CreateBuilder<ObservationMember>();

        foreach (var member in symbol.GetMembers())
        {
            // R4.13: global mutable state is covered by no per-object invariant.
            if (member is IFieldSymbol { IsStatic: true, IsConst: false } stat)
            {
                diagnostics.Error("PALCS0522",
                    Locations.From(stat.Locations.FirstOrDefault() ?? Location.None),
                    $"`{symbol.Name}.{stat.Name}` is a static mutable field. No per-object invariant " +
                    "covers it, so nothing in the scheme can say what it holds.");
                ok = false;
                continue;
            }

            if (Declarations.Has(member, known.SpecAttribute) &&
                Body(member) is { } observationBody &&
                ReturnTypeOf(member) is { } observationType)
            {
                var mappedReturn = known.MapType(observationType);
                if (mappedReturn is null)
                {
                    diagnostics.Error("PALCS0500",
                        Locations.From(member.Locations.FirstOrDefault() ?? Location.None),
                        $"`{symbol.Name}.{member.Name}` returns `{observationType}`, which has no " +
                        "translation.");
                    ok = false;
                    continue;
                }
                observations.Add(new ObservationMember(member, member.Name, mappedReturn, observationBody));
                continue;
            }

            if (SymbolEqualityComparer.Default.Equals(member, modelSymbol)) continue;
            if (member is IMethodSymbol { AssociatedSymbol: not null }) continue;

            var (name, type) = member switch
            {
                IFieldSymbol { IsStatic: false, IsConst: false, AssociatedSymbol: null } f => (f.Name, f.Type),
                IPropertySymbol { IsStatic: false, IsIndexer: false } p when IsAuto(p) => (p.Name, p.Type),
                _ => (null, null),
            };
            if (name is null || type is null) continue;

            var mapped = known.MapType(type);
            if (mapped is null)
            {
                diagnostics.Error("PALCS0500",
                    Locations.From(member.Locations.FirstOrDefault() ?? Location.None),
                    $"The field `{symbol.Name}.{name}` has type `{type}`, which has no translation.");
                ok = false;
                continue;
            }

            // R3.7. A class may own an array where a struct may not (PALCS0511): a class
            // is a heap cell rather than a value, so copying it cannot duplicate
            // ownership. The invariant then carries the array's `A.pts_to` (R3.10a).
            // A field of *class* type is a different matter — it would nest one invariant
            // inside another — and is still refused.
            if (mapped is not (IrPrim or IrNamedType or IrArrayType))
            {
                diagnostics.Error("PALCS0531",
                    Locations.From(member.Locations.FirstOrDefault() ?? Location.None),
                    $"The field `{symbol.Name}.{name}` has type `{type}`. A class may own an array " +
                    "(doc/translation.md R3.10a), but not another object: its invariant would have to " +
                    "contain the other's, and nothing in the scheme says when that one may be opened.");
                ok = false;
                continue;
            }

            fields.Add(new StructField(member, name, type, mapped));
        }

        if (Body(modelSymbol) is not { } modelBody || ReturnTypeOf(modelSymbol) is not { } modelReturn)
        {
            diagnostics.Error("PALCS0524",
                Locations.From(modelSymbol.Locations.FirstOrDefault() ?? Location.None),
                $"`{symbol.Name}`'s `[Model]` member has no expression body. The abstraction function " +
                "must be a single expression over the fields, because it *is* the connection between " +
                "the representation and the model.");
            return false;
        }

        var modelType = known.MapType(modelReturn);
        if (modelType is null)
        {
            diagnostics.Error("PALCS0500",
                Locations.From(modelSymbol.Locations.FirstOrDefault() ?? Location.None),
                $"`{symbol.Name}`'s model has type `{modelReturn}`, which has no translation.");
            return false;
        }

        if (!ok) return false;

        candidate = new ClassCandidate(
            syntax, symbol, fields.ToImmutable(), modelSymbol, modelType, modelBody,
            observations.ToImmutable(), BuildClassUsings(syntax, symbol));
        return true;
    }

    /// <summary>The expression body of a <c>[Model]</c> or <c>[Spec]</c> member.</summary>
    private static ExpressionSyntax? Body(ISymbol member) =>
        member.DeclaringSyntaxReferences.FirstOrDefault()?.GetSyntax() switch
        {
            PropertyDeclarationSyntax { ExpressionBody.Expression: { } e } => e,
            MethodDeclarationSyntax { ExpressionBody.Expression: { } e } => e,
            _ => null,
        };

    private static ITypeSymbol? ReturnTypeOf(ISymbol member) => member switch
    {
        IPropertySymbol p => p.Type,
        IMethodSymbol m => m.ReturnType,
        _ => null,
    };

    /// <summary>
    /// R3.9d: an <c>[Invariant]</c> clause sees the fields as simple names, and a
    /// <c>[Refine]</c> on the <c>[Model]</c> member sees the model value as
    /// <c>Result</c> — the two kinds of fact are bound in different scopes precisely
    /// because they are about different things.
    /// </summary>
    private static ImmutableArray<SpecSite> BuildClassSpecSites(ImmutableArray<ClassCandidate> classes)
    {
        var sites = ImmutableArray.CreateBuilder<SpecSite>();
        foreach (var c in classes)
        {
            var fieldParams = c.Fields.Select(f => new SpecParam(f.Name, f.Type)).ToImmutableArray();
            var index = 0;
            foreach (var (text, location) in ClassInvariants(c))
                sites.Add(new SpecSite(
                    Key: $"{c.Symbol.Name}_invariant_{index++}",
                    Text: text,
                    Location: location,
                    Parameters: fieldParams,
                    Usings: c.Usings));

            index = 0;
            foreach (var (text, location) in ModelRefinements(c))
                sites.Add(new SpecSite(
                    Key: $"{c.Symbol.Name}_model_refine_{index++}",
                    Text: text,
                    Location: location,
                    Parameters: ReturnTypeOf(c.ModelSymbol) is { } mt
                        ? [new SpecParam(SpecBinder.ResultParameter, mt)]
                        : ImmutableArray<SpecParam>.Empty,
                    Usings: c.Usings));
        }
        return sites.ToImmutable();
    }

    private static IEnumerable<(string Text, Location Location)> ClassInvariants(ClassCandidate c)
    {
        foreach (var data in c.Symbol.GetAttributes())
            if (data.AttributeClass?.Name == "InvariantAttribute" &&
                Declarations.StringArgument(data) is { } text)
                yield return (text, Declarations.ArgumentLocation(data));
    }

    /// <summary>Whether a lowered class-level clause reads at least one field (R3.9d).</summary>
    private static bool MentionsAField(IrExpr expr, ImmutableHashSet<string> fields)
    {
        var found = false;
        Walk(expr);
        return found;

        void Walk(IrExpr? e)
        {
            if (e is null || found) return;
            switch (e)
            {
                case IrVar v when fields.Contains(v.Name): found = true; return;
                case IrUnary u: Walk(u.Operand); return;
                case IrBinary b: Walk(b.Left); Walk(b.Right); return;
                case IrConditional c: Walk(c.Cond); Walk(c.Then); Walk(c.Else); return;
                case IrElement el: Walk(el.Array); Walk(el.Index); return;
                case IrLength l: Walk(l.Array); return;
                case IrField f: Walk(f.Receiver); return;
                case IrObserve o: Walk(o.Receiver); return;
                case IrConvert cv: Walk(cv.Operand); return;
                case IrOld o2: Walk(o2.Operand); return;
                case IrLive lv: Walk(lv.Operand); return;
                case IrNewArray na: Walk(na.Length); return;
                case IrContents ct: Walk(ct.Array); return;
                case IrQuantifier q: Walk(q.Body); return;
                case IrCall call: foreach (var a in call.Args) Walk(a); return;
                case IrSeqOp so: foreach (var a in so.Args) Walk(a); return;
                case IrNew n: foreach (var f2 in n.Fields) Walk(f2.Value); return;
                // Raw Pulse is opaque, so it is taken at its word rather than refused.
                case IrInlinePulse: found = true; return;
                default: return;
            }
        }
    }

    private static IEnumerable<(string Text, Location Location)> ModelRefinements(ClassCandidate c)
    {
        foreach (var data in c.ModelSymbol.GetAttributes())
            if (data.AttributeClass?.Name is "RefineAttribute" or "RefineAlwaysAttribute" &&
                Declarations.StringArgument(data) is { } text)
                yield return (text, Declarations.ArgumentLocation(data));
    }

    private static IrClass LowerClass(
        ClassCandidate c,
        WellKnown known,
        ImmutableDictionary<string, BoundSpec> bound,
        SemanticModel classModel,
        DiagnosticBag diagnostics)
    {
        var fields = c.Fields
            .Select(f => new IrFieldDecl(
                Locations.From(f.Symbol.Locations.FirstOrDefault() ?? Location.None), f.Name, f.Mapped))
            .ToImmutableArray();

        // The abstraction reads the fields; an observation reads the model. Both are
        // written unqualified inside the class, which is the same convention R3.4 uses
        // for a struct's [Refine].
        var fieldNames = c.Fields.Select(f => f.Name).ToImmutableHashSet();
        var modelName = ImmutableHashSet.Create(c.ModelSymbol.Name);

        var modelBody = new ExprLowerer(classModel, known, diagnostics, specPosition: true)
        { ClassMembers = fieldNames }.Lower(c.ModelBody);

        var invariants = ImmutableArray.CreateBuilder<IrExpr>();
        var invariantTexts = ClassInvariants(c).ToImmutableArray();
        for (var i = 0; i < invariantTexts.Length; i++)
        {
            if (!bound.TryGetValue($"{c.Symbol.Name}_invariant_{i}", out var spec)) continue;
            var clause = new ExprLowerer(spec.Model, known, diagnostics, specPosition: true)
                .Lower(spec.Expression);

            // R3.9d / F17. A clause that names no field is a fact about the model alone,
            // and inside the invariant it is unreachable: a caller holds the invariant
            // opaquely, so the fact is true and useless. It belongs on the model, as a
            // [Refine], where it becomes part of the model *type* and so travels with
            // every model the caller ever sees. Refusing it is the only way the user
            // finds out, because the wrong placement still verifies here and fails much
            // later, in the client.
            if (!MentionsAField(clause, fieldNames))
                diagnostics.Error("PALCS0527",
                    Locations.From(invariantTexts[i].Location),
                    $"This `[Invariant]` on `{c.Symbol.Name}` mentions no field, so it says something " +
                    "about the model alone. Inside the invariant no caller can reach it. Move it to " +
                    $"`[Refine]` on the `[Model]` member `{c.ModelSymbol.Name}`, writing the model as " +
                    "`Result`.");

            invariants.Add(clause);
        }

        var refinements = ImmutableArray.CreateBuilder<IrExpr>();
        for (var i = 0; i < ModelRefinements(c).Count(); i++)
            if (bound.TryGetValue($"{c.Symbol.Name}_model_refine_{i}", out var spec))
                refinements.Add(new ExprLowerer(spec.Model, known, diagnostics, specPosition: true)
                    .Lower(spec.Expression));

        var observations = c.Observations
            .Select(o => new IrObservation(
                Locations.From(o.Symbol.Locations.FirstOrDefault() ?? Location.None),
                o.Name,
                o.ReturnType,
                new ExprLowerer(classModel, known, diagnostics, specPosition: true)
                { ClassMembers = modelName }.Lower(o.Body)))
            .ToImmutableArray();

        return new IrClass(
            Locations.From(c.Syntax.Identifier), c.Symbol.Name, fields,
            c.ModelSymbol.Name, c.ModelType, modelBody, refinements.ToImmutable(), invariants.ToImmutable(), observations);
    }

    private static ImmutableArray<string> BuildClassUsings(
        ClassDeclarationSyntax syntax, INamedTypeSymbol symbol)
    {
        var fileUsings = syntax.SyntaxTree.GetRoot()
            .DescendantNodes()
            .OfType<UsingDirectiveSyntax>()
            .Select(u => u.ToString())
            .ToImmutableArray();

        var ns = symbol.ContainingNamespace;
        var enclosing = ns is null || ns.IsGlobalNamespace
            ? ImmutableArray<string>.Empty
            : ImmutableArray.Create($"using {ns.ToDisplayString()};");

        return
        [
            .. fileUsings,
            .. enclosing,
            $"using {WellKnown.Namespace};",
            $"using static {WellKnown.Namespace}.Pal;",
        ];
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
                    Key: $"{Naming.Of(candidate.Symbol)}_{index}",
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

        // R4.10a. A spec string is compiled as the body of a *static* shim method, where
        // a bare `this` is C# error CS0026, so the receiver has to be an ordinary
        // parameter. Naming it `this` makes it render as the verbatim identifier `@this`
        // (SpecBinder.RenderParam), which is legal C#, binds correctly, and needs no
        // machinery of its own. A constructor has no receiver in its contract: the object
        // does not exist until it returns, and R4.12 constrains the *initial model*
        // through `Result` instead.
        if (symbol is { IsStatic: false, MethodKind: MethodKind.Ordinary or MethodKind.Constructor })
            result.Add(new SpecParam(Names.This, symbol.ContainingType));

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
        var loc = Locations.From(candidate.Identifier);

        var specs = ReadSpecs(symbol, known, bound, diagnostics);
        var parameters = LowerParameters(symbol, known, diagnostics);
        if (symbol is { IsStatic: false, MethodKind: MethodKind.Ordinary, ContainingType: { } self } &&
            known.HasModel(self))
        {
            parameters = [new IrParam(loc, Names.This, new IrClassType(self.Name), ParamMode.Value),
                          .. parameters];
        }

        if (candidate.Kind == CalleeKind.Spec)
            return LowerSpecFunction(candidate, model, known, diagnostics, loc, parameters, specs);

        var returnType = symbol.MethodKind == MethodKind.Constructor
            ? new IrClassType(symbol.ContainingType.Name)
            : known.MapType(symbol.ReturnType);
        if (returnType is null)
        {
            diagnostics.Unsupported(loc, $"The return type `{symbol.ReturnType}`");
            return null;
        }

        var declaringClass = symbol is { IsStatic: false, ContainingType: { } owner } && known.HasModel(owner)
            ? owner.Name
            : null;

        var objectFields = symbol.ContainingType is not { } holder || !known.HasModel(holder)
            ? ImmutableHashSet<string>.Empty
            : holder.GetMembers().OfType<IFieldSymbol>()
                .Where(f => !f.IsStatic && !f.IsImplicitlyDeclared)
                .Select(f => f.Name)
                .ToImmutableHashSet();

        var lowerer = new StmtLowerer(model, known, diagnostics, objectFields);
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
            DeclaringClass = declaringClass,
            IsConstructor = symbol.MethodKind == MethodKind.Constructor,
            IsReadOnly = declaringClass is not null &&
                symbol.MethodKind != MethodKind.Constructor &&
                !Declarations.Mutates(candidate.Syntax, model),
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

        var bodyExpression = candidate.ExpressionBody?.Expression
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

    private static IrStmt? LowerBody(BaseMethodDeclarationSyntax syntax, StmtLowerer lowerer)
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
            var key = $"{Naming.Of(symbol)}_{index}";
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
            BaseMethodDeclarationSyntax syntax, SemanticModel model, WellKnown known, StmtLowerer lowerer)
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
