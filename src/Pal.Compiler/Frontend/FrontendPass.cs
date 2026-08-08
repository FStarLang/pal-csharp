using System.IO;
using System.Text.RegularExpressions;
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
        ValidateSpecTypes(compilation, known, diagnostics);
        var candidates = Collect(compilation, known);
        var structs = CollectStructs(compilation, known, diagnostics);
        var attempted = ImmutableHashSet.CreateBuilder<ISymbol>(SymbolEqualityComparer.Default);
        var classes = CollectClasses(compilation, known, diagnostics, attempted);
        ReportUncollected(compilation, known, classes, attempted.ToImmutable(), diagnostics);
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

        foreach (var include in CollectIncludes(compilation, known, diagnostics))
            declarations.Add(include);

        InheritContracts(declarations, diagnostics);
        return new IrProgram(declarations.ToImmutable());
    }

    /// <summary>
    /// R9.7. A virtual method's contract is written once, on the <c>abstract</c>
    /// declaration, and every <c>override</c> is checked against it. So the override's IR
    /// is given its parent's clauses here, before anything downstream can see the
    /// difference — the emitter never has to ask which of the two a clause came from, and
    /// there is no way for a subclass to weaken what its callers were promised.
    /// </summary>
    private static void InheritContracts(
        ImmutableArray<IrDecl>.Builder declarations, DiagnosticBag diagnostics)
    {
        var byName = declarations.OfType<IrMethod>()
            .Where(m => m.IsAbstract && m.DeclaringClass is not null)
            .ToDictionary(m => m.Name);
        // R9.18. `Overrides` names the *immediate* base, because that is the class whose
        // model the override's vtable slot is typed at. It is not necessarily the class
        // that *declared* the method: at depth three `Square.GetArea` overrides through
        // `Quadrilateral`, which declares no `GetArea` of its own. So the contract is
        // looked up by walking, and the two questions — whose model, and whose contract —
        // are answered separately, which is what they always were.
        var bases = declarations.OfType<IrClass>()
            .Where(c => c.BaseClass is not null)
            .ToDictionary(c => c.Name, c => c.BaseClass!);

        for (var i = 0; i < declarations.Count; i++)
        {
            if (declarations[i] is not IrMethod
                { Overrides: { } baseName, DeclaringClass: not null } o) continue;
            IrMethod? found = null;
            for (var at = baseName; at is not null; at = bases.TryGetValue(at, out var up) ? up : null)
                if (byName.TryGetValue($"{at}_{Member(o)}", out var candidate))
                {
                    found = candidate;
                    break;
                }
            if (found is not { } v) continue;

            if (o.Requires.Length + o.Ensures.Length + o.Preserves.Length > 0)
            {
                diagnostics.Error("PALCS0544", o.Loc,
                    $"`{o.Name}` overrides `{v.Name}` and carries its own contract. A virtual " +
                    "method's contract belongs on the `abstract` declaration, where it is written " +
                    "once and every caller of the base class can see it; a contract here would be " +
                    "one the caller has no way to know applies (doc/translation.md R9.7).");
                continue;
            }

            var mismatched = false;
            for (var k = 0; k < Math.Min(o.Parameters.Length, v.Parameters.Length); k++)
            {
                if (o.Parameters[k].Name == v.Parameters[k].Name) continue;
                diagnostics.Error("PALCS0544", o.Parameters[k].Loc,
                    $"`{o.Name}` names its parameter `{o.Parameters[k].Name}` where `{v.Name}` " +
                    $"names it `{v.Parameters[k].Name}`. The inherited contract is written in terms " +
                    "of the base declaration's parameter names, so the two must agree.");
                mismatched = true;
            }
            if (mismatched) continue;

            declarations[i] = o with
            {
                Requires = v.Requires,
                Ensures = v.Ensures,
                Preserves = v.Preserves,
                IsReadOnly = v.IsReadOnly,
            };
        }
    }

    /// <summary>The member's own name, with the qualifier <see cref="Naming.Of"/> added.</summary>
    private static string Member(IrMethod m) =>
        m.DeclaringClass is { } c && m.Name.StartsWith(c + "_", StringComparison.Ordinal)
            ? m.Name[(c.Length + 1)..]
            : m.Name;

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
                // R11.1a. A specification type's members declare F* names; they are not
                //程 code and have no bodies to translate.
                if (known.IsSpecTypeDeclaration(symbol.ContainingType)) continue;
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
        ImmutableArray<ClassCandidate> classes, ImmutableHashSet<ISymbol> attempted,
        DiagnosticBag diagnostics)
    {
        var translated = classes
            .Select(c => (ISymbol)c.Symbol)
            .ToImmutableHashSet(SymbolEqualityComparer.Default)
            .Union(attempted);

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

                // R11.1a. A specification-type declaration is not a class and not a class
                // member; its members declare F* names.
                if (known.IsSpecTypeDeclaration(symbol as INamedTypeSymbol ?? symbol.ContainingType))
                    continue;

                // A class whose own declaration carries [Invariant] or [Model], or an
                // annotated instance member of one: all of these are §3.4, not yet built.
                var isClassMember =
                    symbol is INamedTypeSymbol { TypeKind: TypeKind.Class }
                        ? Declarations.IsAnnotated(symbol, known)
                        : symbol is { IsStatic: false, ContainingType.TypeKind: TypeKind.Class or TypeKind.Interface }
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
                    $"`{symbol.Name}` carries a pal-csharp annotation, but the type declaring it is " +
                    "not one the translator collected. A translated class is a `class` declaration " +
                    "with a `[Model]` member (doc/translation.md §3.4); a `record`, a `struct` " +
                    "member reached this way, or a class whose declaration the collector never saw " +
                    "is none of those, so the annotation would be silently dropped (R18.1).");
            }
        }
    }

    private static IEnumerable<IrIncludePulse> CollectIncludes(
        Compilation compilation, WellKnown known, DiagnosticBag diagnostics)
    {
        foreach (var data in Declarations.All(compilation.Assembly, known.IncludePulseAttribute))
        {
            var module = Declarations.StringArgument(data, 0);
            var body = Declarations.StringArgument(data, 1);
            if (module is null || body is null) continue;
            yield return new IrIncludePulse(
                Locations.From(Declarations.ArgumentLocation(data)), module, body);
        }

        foreach (var data in Declarations.All(compilation.Assembly, known.IncludePulseFileAttribute))
        {
            var include = ReadIncludeFile(data, diagnostics);
            if (include is not null) yield return include;
        }
    }

    /// <summary>
    /// R12.6. Reads an <c>[IncludePulseFile]</c>. The module name is the file's base name
    /// rather than a second argument, and the file's own <c>module</c> header is checked
    /// against it: a Pulse module that is emitted under one name and declares another is a
    /// verification failure two passes later, pointing at generated output rather than at
    /// the attribute that caused it.
    /// </summary>
    private static IrIncludePulse? ReadIncludeFile(AttributeData data, DiagnosticBag diagnostics)
    {
        var location = Locations.From(Declarations.ArgumentLocation(data));
        var relative = Declarations.StringArgument(data, 0);
        if (relative is null) return null;

        var declaring = data.ApplicationSyntaxReference?.SyntaxTree.FilePath;
        var directory = string.IsNullOrEmpty(declaring)
            ? Directory.GetCurrentDirectory()
            : Path.GetDirectoryName(Path.GetFullPath(declaring!))!;
        var full = Path.GetFullPath(Path.Combine(directory, relative));

        if (!File.Exists(full))
        {
            diagnostics.Error("PALCS0583", location,
                $"`[IncludePulseFile(\"{relative}\")]` names `{full}`, which does not exist. " +
                "The path is resolved relative to the directory of the C# file carrying the " +
                "attribute (doc/translation.md R12.6).");
            return null;
        }

        var module = Path.GetFileNameWithoutExtension(full);
        string text;
        try
        {
            text = File.ReadAllText(full);
        }
        catch (IOException e)
        {
            diagnostics.Error("PALCS0583", location,
                $"`[IncludePulseFile(\"{relative}\")]` names `{full}`, which could not be read: " +
                e.Message);
            return null;
        }

        var declared = Regex.Match(text, @"(?m)^\s*module\s+([A-Za-z0-9_.]+)");
        if (declared.Success && declared.Groups[1].Value != module)
        {
            diagnostics.Error("PALCS0584", location,
                $"`{full}` declares `module {declared.Groups[1].Value}`, but pal-csharp emits it " +
                $"as `{module}` — the module name is the file's base name, so that the two cannot " +
                "drift (doc/translation.md R12.6). Rename the file or the `module` header so they " +
                "agree.");
            return null;
        }

        return new IrIncludePulse(location, module, text);
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

    /// <summary>
    /// R11.1b. Checks that the three specification-type attributes are where they claim to
    /// be, <em>before</em> R11.1a makes their declarations invisible to every other pass.
    ///
    /// <para>This has to be its own pass. A specification-type declaration is skipped
    /// wholesale, so nothing downstream ever sees it; without this, an attribute in the
    /// wrong place would be silently ignored, and the first sign of it would be a use of
    /// the member failing with PALCS0573 — a message about the use, pointing away from the
    /// mistake.</para>
    /// </summary>
    private static void ValidateSpecTypes(
        CSharpCompilation compilation, WellKnown known, DiagnosticBag diagnostics)
    {
        foreach (var tree in compilation.SyntaxTrees)
        {
            var model = compilation.GetSemanticModel(tree);
            foreach (var syntax in tree.GetRoot().DescendantNodes().OfType<TypeDeclarationSyntax>())
            {
                if (model.GetDeclaredSymbol(syntax) is not { } type) continue;

                // R11.5. A `[SpecType]` denotes an F* type and has no representation: no
                // fields to own, no model to abstract it by, nothing to construct. Saying
                // it is also a translated class asks for both at once.
                if (known.SpecTypeName(type) is not null)
                {
                    var offender =
                        type.GetMembers().FirstOrDefault(m => Declarations.Has(m, known.ModelAttribute))
                        ?? type.GetMembers().FirstOrDefault(m => Declarations.Has(m, known.InvariantAttribute));
                    if (offender is not null)
                        diagnostics.Error("PALCS0570", Locations.From(syntax.Identifier),
                            $"The type `{type.Name}` is a `[SpecType]`, so it denotes the F* type " +
                            $"`{known.SpecTypeName(type)}` and has no representation of its own. " +
                            $"Remove `[{(Declarations.Has(offender, known.ModelAttribute) ? "Model" : "Invariant")}]` " +
                            $"from `{offender.Name}`, or remove `[SpecType]`.");
                }

                foreach (var member in type.GetMembers())
                {
                    // R11.2. `[SpecOp]` says "this member reads as this F* term applied to
                    // the receiver". Off a specification type there is no such receiver.
                    // R12.2. An `SlProp`-valued `[SpecOp]` is an *ownership predicate*, not
                    // an operation on a specification type: it belongs to no type, because
                    // what it describes is a region of the heap. It is therefore allowed
                    // wherever a static method is.
                    var isPredicate = member is IMethodSymbol { IsStatic: true } pm &&
                        SymbolEqualityComparer.Default.Equals(pm.ReturnType, known.SlProp);

                    if (known.SpecOpName(member) is not null && known.SpecTypeName(type) is null &&
                        !isPredicate &&
                        !(member.IsStatic && type.GetMembers().Any(m => known.SpecCtorName(m) is not null)))
                        diagnostics.Error("PALCS0571", MemberLocation(member, syntax),
                            $"`[SpecOp]` on `{type.Name}.{member.Name}`, but `{type.Name}` is not a " +
                            $"`[SpecType]`. An operation belongs either to the specification type it " +
                            $"reads, or to the class that declares that type's `[SpecCtor]`s.");

                    // R11.3. A constructor's whole job is to produce a value of the
                    // specification type; if it does not, the emitted application is
                    // ill-typed in F* and the C# says something the F* does not.
                    if (known.SpecCtorName(member) is not null)
                    {
                        var returns = member is IMethodSymbol m ? m.ReturnType : null;
                        if (!member.IsStatic || known.SpecTypeName(returns) is null)
                            diagnostics.Error("PALCS0571", MemberLocation(member, syntax),
                                $"`[SpecCtor]` on `{type.Name}.{member.Name}`, which is not a static " +
                                $"method returning a `[SpecType]`. A specification constructor builds a " +
                                $"value of the type it constructs.");
                    }
                }
            }
        }
    }

    private static IrLoc MemberLocation(ISymbol member, TypeDeclarationSyntax fallback) =>
        member.DeclaringSyntaxReferences.FirstOrDefault()?.GetSyntax() is MemberDeclarationSyntax d
            ? Locations.From(d)
            : Locations.From(fallback.Identifier);

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
                if (known.IsSpecTypeDeclaration(symbol)) continue;   // R11.1a
                if (RefuseGenericType(symbol, diagnostics)) continue;

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
            TypeParameters = [.. s.Symbol.TypeParameters.Select(t => t.Name)],
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
        ExpressionSyntax? ModelBody,
        ImmutableArray<ObservationMember> Observations,
        ImmutableArray<string> Usings)
    {
        /// <summary>R9.1. The translated base class, if this class derives from one.</summary>
        public INamedTypeSymbol? BaseSymbol { get; init; }

        /// <summary>R9.2. An <c>abstract class</c>: a vtable rather than a record.</summary>
        public bool IsAbstract { get; init; }

        /// <summary>R12.1. <c>[Plain]</c>: representation only, no derived ownership.</summary>
        public bool IsPlain { get; init; }

        /// <summary>R9.6. The <c>override</c> of the base's <c>[Model]</c> — the forgetting function.</summary>
        public ExpressionSyntax? ForgetBody { get; init; }

    }

    /// <summary>
    /// Collects every annotated <c>sealed class</c>. A class is annotated when it carries
    /// a <c>[Model]</c> member, which R3.9 makes mandatory: without one there is nothing
    /// for the invariant to relate the representation to, and every method specification
    /// would collapse to memory safety.
    /// </summary>
    private static ImmutableArray<ClassCandidate> CollectClasses(
        CSharpCompilation compilation, WellKnown known, DiagnosticBag diagnostics,
        ImmutableHashSet<ISymbol>.Builder attempted)
    {
        var result = ImmutableArray.CreateBuilder<ClassCandidate>();
        foreach (var tree in compilation.SyntaxTrees)
        {
            var model = compilation.GetSemanticModel(tree);
            foreach (var syntax in tree.GetRoot().DescendantNodes().OfType<ClassDeclarationSyntax>())
            {
                if (model.GetDeclaredSymbol(syntax) is not { } symbol) continue;
                if (symbol.IsStatic) continue;
                if (RefuseGenericType(symbol, diagnostics)) continue;

                // R18.1. Every class the collector *looks at* is one it has spoken about:
                // if it rejects the class, the rejection is the diagnostic, and the
                // members must not then draw PALCS0530 as well. Recording the attempt is
                // what keeps one cause from producing a second, contradictory report.
                if (Declarations.Has(symbol, known.PlainAttribute) ||
                    symbol.GetMembers().Any(m => Declarations.Has(m, known.ModelAttribute)))
                    attempted.Add(symbol);

                var modelMembers = symbol.GetMembers()
                    .Where(m => Declarations.Has(m, known.ModelAttribute))
                    .ToImmutableArray();

                // R12.1. A `[Plain]` class is collected for its *representation* alone. It
                // has no model, so none of the checks below apply to it: they all ask
                // whether the abstraction function is well formed, and it has none by
                // construction. What owns its cells is whatever the user's own predicate
                // says, which the translator never sees.
                if (Declarations.Has(symbol, known.PlainAttribute))
                {
                    if (modelMembers.Length > 0)
                    {
                        diagnostics.Error("PALCS0574", Locations.From(syntax.Identifier),
                            $"`{symbol.Name}` is `[Plain]` and also declares a `[Model]`. " +
                            "`[Plain]` means the class has no derived ownership at all, so there is " +
                            "nothing for an abstraction function to abstract. Drop one of the two: " +
                            "keep `[Model]` for a class whose predicate the translator derives, and " +
                            "`[Plain]` for one whose predicate you write yourself " +
                            "(doc/translation.md R12.1).");
                        continue;
                    }
                    if (symbol.IsAbstract || symbol.BaseType?.SpecialType != SpecialType.System_Object)
                    {
                        diagnostics.Error("PALCS0575", Locations.From(syntax.Identifier),
                            $"`{symbol.Name}` is `[Plain]` and takes part in a class hierarchy. " +
                            "A `[Plain]` class is a bare representation with no vtable and no " +
                            "invariant to relate to a base class's, so the two encodings have nothing " +
                            "to compose. Make it `sealed` and free-standing.");
                        continue;
                    }
                    if (CollectPlainFields(symbol, known, diagnostics) is not { } plainFields)
                        continue;
                    result.Add(new ClassCandidate(
                        syntax, symbol, plainFields, symbol, IrPrim.SpecIntType, null,
                        [], BuildClassUsings(syntax, symbol))
                    {
                        IsPlain = true,
                    });
                    continue;
                }

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

                // R9.1/R9.4. A class is either a leaf — `sealed`, with a representation —
                // or `abstract`, with a vtable and none. Anything else is a vtable value
                // and a vtable type at once, which neither design study builds.
                if (!symbol.IsSealed && !symbol.IsAbstract)
                {
                    diagnostics.Error("PALCS0521", Locations.From(syntax.Identifier),
                        $"`{symbol.Name}` is neither `sealed` nor `abstract`. A translated class is " +
                        "either a leaf, which owns a representation, or an abstract base, which owns a " +
                        "vtable (doc/translation.md R9.4). A class that is both would have to be its " +
                        "own subclass's vtable type and one of its values at the same time.");
                    continue;
                }

                if (!TryCollectClass(syntax, symbol, modelMembers[0], known, diagnostics, out var candidate))
                    continue;
                result.Add(candidate);
            }
        }
        return result.ToImmutable();
    }

    /// <summary>
    /// R12.1. The fields of a <c>[Plain]</c> class. Only the representation is wanted, so
    /// this is the struct field rule (R3.4) and nothing else: every instance field and
    /// auto-property, mapped, with no model, no observations and no invariant to check.
    /// </summary>
    private static ImmutableArray<StructField>? CollectPlainFields(
        INamedTypeSymbol symbol, WellKnown known, DiagnosticBag diagnostics)
    {
        var fields = ImmutableArray.CreateBuilder<StructField>();
        var ok = true;
        foreach (var member in symbol.GetMembers())
        {
            if (member is IFieldSymbol { IsStatic: true, IsConst: false } stat)
            {
                diagnostics.Error("PALCS0522",
                    Locations.From(stat.Locations.FirstOrDefault() ?? Location.None),
                    $"`{symbol.Name}.{stat.Name}` is a static mutable field. No per-object " +
                    "invariant covers it, so nothing in the scheme can say what it holds.");
                ok = false;
                continue;
            }

            var (name, type) = member switch
            {
                IFieldSymbol { IsStatic: false, IsConst: false, AssociatedSymbol: null } f
                    => (f.Name, f.Type),
                IPropertySymbol { IsStatic: false, IsIndexer: false } p
                    when p.GetMethod is not null && IsAuto(p) => (p.Name, p.Type),
                _ => (null, null),
            };
            if (name is null || type is null) continue;

            if (known.MapType(type) is not { } mapped)
            {
                diagnostics.Error("PALCS0500",
                    Locations.From(member.Locations.FirstOrDefault() ?? Location.None),
                    $"`{symbol.Name}.{name}` has type `{type}`, which has no translation.");
                ok = false;
                continue;
            }
            fields.Add(new StructField(member, name, type, mapped));
        }
        return ok ? fields.ToImmutable() : null;
    }

    /// <summary>
    /// R18.1. Every member of a translated class is accounted for, or refused by name.
    /// </summary>
    /// <remarks>
    /// <see cref="TryCollectClass"/> and <see cref="Collect"/> both match positively: a
    /// field, an auto-property, the <c>[Model]</c>, a <c>[Spec]</c> observation, an
    /// ordinary method, a constructor. Whatever matched none of those used to fall out of
    /// the loop, and the class was translated as though the member had not been written.
    /// A computed property, an indexer, a <c>const</c>, an operator and an
    /// <c>override</c> of an <c>object</c> member all took that exit — silently, with
    /// `palcs` reporting success, which is the one outcome the whole diagnostics
    /// philosophy (R2.3) exists to prevent.
    ///
    /// The categories below are the accepting ones and nothing else is, so a construct C#
    /// grows tomorrow is refused by default rather than dropped by default. That is the
    /// entire content of the rule: the walk is total.
    /// </remarks>
    private static bool ReportUnaccountedMembers(
        INamedTypeSymbol symbol, ISymbol modelSymbol, WellKnown known, DiagnosticBag diagnostics)
    {
        var ok = true;
        foreach (var member in symbol.GetMembers())
        {
            // Roslyn synthesises a backing field, an implicit constructor and the accessor
            // pair of every property. None was written by the user, so none is a construct
            // to refuse; each is accounted for by the member it belongs to.
            if (member.IsImplicitlyDeclared) continue;
            if (SymbolEqualityComparer.Default.Equals(member, modelSymbol)) continue;
            if (Declarations.IsAnnotated(member, known)) continue;
            if (member.IsOverride && OverriddenChainHasModel(member, known)) continue;

            // An accessor is reported through the property it belongs to, once. Reporting
            // it again under its own name (`get_Doubled`) would name a symbol the user
            // never wrote and would say the same thing twice.
            if (member is IMethodSymbol { AssociatedSymbol: { } owner })
            {
                if (SymbolEqualityComparer.Default.Equals(owner, modelSymbol)) continue;
                if (Declarations.IsAnnotated(owner, known)) continue;
                if (owner.IsOverride && OverriddenChainHasModel(owner, known)) continue;
                continue;
            }

            var (why, what) = member switch
            {
                // Accounted for: a field (R3.4/R3.10), an auto-property standing for one,
                // an ordinary method or constructor (§4.5), an accessor of a property that
                // is itself accounted for.
                IFieldSymbol { IsStatic: false, IsConst: false, AssociatedSymbol: null } => (null, null),
                IFieldSymbol { IsStatic: true, IsConst: false } => (null, null),   // PALCS0522
                IPropertySymbol { IsStatic: false, IsIndexer: false } p when IsAuto(p) => (null, null),
                IMethodSymbol { MethodKind: MethodKind.Constructor } => (null, null),
                IMethodSymbol { MethodKind: MethodKind.Ordinary, IsOverride: true } m
                    when IsObjectMember(m) =>
                    ("an `override` of a member of `object`. R9.6 reads an `override` as the " +
                     "forgetting function of a translated base, and `System.Object` has no model " +
                     "(doc/translation.md R18.2), so this override has no other reading",
                     $"{symbol.Name}.{member.Name}"),
                IMethodSymbol { MethodKind: MethodKind.Ordinary } => (null, null),

                IPropertySymbol { IsIndexer: true } =>
                    ("an indexer. Indexing a translated object has no rule: `a[i]` is the array " +
                     "subscript of R6.5 and nothing else (doc/translation.md R18.2)",
                     $"{symbol.Name}.this[]"),
                IPropertySymbol =>
                    ("a property with an accessor body. An *auto*-property is a field (R3.4) and a " +
                     "`[Spec]` property is an observation (R3.9c), but a computed property's " +
                     "accessors are methods and no rule emits them yet (doc/translation.md R18.2). " +
                     "Write the accessor as an ordinary method",
                     $"{symbol.Name}.{member.Name}"),
                IFieldSymbol { IsConst: true } =>
                    ("a `const` field. It owns nothing, so it needs no invariant, but nothing yet " +
                     "puts its value in scope in a body or a contract (doc/translation.md R18.2)",
                     $"{symbol.Name}.{member.Name}"),
                IMethodSymbol { MethodKind: MethodKind.ExplicitInterfaceImplementation } =>
                    ("an explicit interface implementation, and §9 has no interfaces " +
                     "(doc/translation.md R18.2)", $"{symbol.Name}.{member.Name}"),
                IMethodSymbol { MethodKind: MethodKind.UserDefinedOperator or MethodKind.Conversion } =>
                    ("a user-defined operator. R6.4 reads an operator from its operand type, and an " +
                     "operator declaration would have to add a case to that rule " +
                     "(doc/translation.md R18.2)", $"{symbol.Name}.{member.Name}"),
                IMethodSymbol { MethodKind: MethodKind.Destructor } =>
                    ("a finalizer. Object lifecycle wants a state-indexed invariant and §3.4 has " +
                     "only `class_C__inv this m` (doc/translation.md §8.5)",
                     $"{symbol.Name}.~{symbol.Name}"),
                IEventSymbol =>
                    ("an event. A delegate is outside the supported subset " +
                     "(doc/translation.md §8.5)", $"{symbol.Name}.{member.Name}"),
                INamedTypeSymbol => (null, null),   // a nested type is walked on its own

                _ => ($"a {member.Kind} member with no rule (doc/translation.md R18.1)",
                      $"{symbol.Name}.{member.Name}"),
            };

            if (why is null) continue;
            diagnostics.Error("PALCS0591",
                Locations.From(member.Locations.FirstOrDefault() ?? Location.None),
                $"`{what}` is {why}. It is a member of a translated class, so leaving it out of the " +
                "translation would prove a theorem about a different program; it is refused instead.");
            ok = false;
        }
        return ok;
    }

    /// <summary>
    /// Whether an <c>override</c> targets a member `object` declares. Every C# class
    /// derives from `System.Object` implicitly, so `BaseType.Name` is `"Object"` for a
    /// class with no user base — which is how `override int GetHashCode()` came to emit a
    /// reference to a `Class_Object` module that is never generated (R18.2).
    /// </summary>
    private static bool IsObjectMember(IMethodSymbol method)
    {
        for (var m = method; m is not null; m = m.OverriddenMethod)
            if (m.ContainingType?.SpecialType == SpecialType.System_Object) return true;
        return false;
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
            // R9.6. The override of the base's [Model] is the forgetting function, not a
            // field and not an observation; it is collected separately below.
            if (member.IsOverride && OverriddenChainHasModel(member, known)) continue;

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
                // R3.10b makes this the likely first mistake: a class is translated exactly
                // when it declares a [Model], so a field of an *unannotated* class type
                // fails the type map rather than the ownership rule, and the generic
                // message would send the user looking in the wrong place.
                var why = type is INamedTypeSymbol { TypeKind: TypeKind.Class }
                    ? $"`{type}` declares no [Model] member, so it has no model for this class's " +
                      "invariant to own (doc/translation.md R3.10b). Give it one, or hold something else."
                    : "which has no translation.";
                diagnostics.Error("PALCS0500",
                    Locations.From(member.Locations.FirstOrDefault() ?? Location.None),
                    $"The field `{symbol.Name}.{name}` has type `{type}`: {why}");
                ok = false;
                continue;
            }

            // R3.7. A class may own an array where a struct may not (PALCS0511): a class
            // is a heap cell rather than a value, so copying it cannot duplicate
            // ownership. The invariant then carries the array's `A.pts_to` (R3.10a), and by
            // R3.10b it carries a sub-object's `class_D__inv` the same way. What is still
            // refused is a field with no ownership story at all — a `Seq`, a `Ghost`, an
            // unannotated class — because there is nothing for the invariant to hold.
            // R15.5. A field at a type parameter is a value like any other: it is not an
            // array and not an object, so the invariant owns it by holding it in the
            // record, and its model is itself.
            if (mapped is not (IrPrim or IrNamedType or IrArrayType or IrClassType or IrTypeParamType))
            {
                diagnostics.Error("PALCS0531",
                    Locations.From(member.Locations.FirstOrDefault() ?? Location.None),
                    $"The field `{symbol.Name}.{name}` has type `{type}`. A class may own a value, " +
                    "an array (doc/translation.md R3.10a) or another annotated object (R3.10b), but " +
                    $"`{type}` is none of those, so its invariant has nothing to hold.");
                ok = false;
                continue;
            }

            fields.Add(new StructField(member, name, type, mapped));
        }

        // R18.1. The loop above matches positively, so every member it did not recognise
        // fell through the `continue` and left the translation without a word. Saying so
        // is the rule; the categories it accepts are exactly the ones the loop collects.
        if (!ReportUnaccountedMembers(symbol, modelSymbol, known, diagnostics)) ok = false;

        // R18.1. A field initialiser runs before the constructor body, and R4.12 builds the
        // representation from the constructor's assignments alone. Ignoring the initialiser
        // and then reporting the field uninitialised named the wrong cause.
        foreach (var member in symbol.GetMembers().OfType<IFieldSymbol>())
        {
            if (member is { IsStatic: false, IsConst: false, AssociatedSymbol: null } &&
                member.DeclaringSyntaxReferences.FirstOrDefault()?.GetSyntax()
                    is VariableDeclaratorSyntax { Initializer: { } init })
            {
                diagnostics.Error("PALCS0596", Locations.From(init.GetLocation()),
                    $"`{symbol.Name}.{member.Name}` has a field initialiser. The representation is " +
                    "built by the constructor (doc/translation.md R4.12), which is the one place the " +
                    "invariant is established, and an initialiser assigns before it runs with no rule " +
                    $"to say so (R18.1). Move the value into the constructor: `this.{member.Name} = …;`.");
                ok = false;
            }
        }

        // R9.2. An abstract class has no representation: the fields are entirely the
        // leaf's. A base field would make a leaf's representation an extension of the
        // base's and force a constructor chain, which neither design study probed.
        if (symbol.IsAbstract && fields.Count > 0)
        {
            diagnostics.Error("PALCS0541",
                Locations.From(fields[0].Symbol.Locations.FirstOrDefault() ?? Location.None),
                $"`{symbol.Name}.{fields[0].Name}` is a field of an `abstract` class. An abstract " +
                "class in the scheme owns a vtable and no representation (doc/translation.md R9.2), " +
                "so there is nothing for this field to live in. Move it to each subclass, or make " +
                "it an `abstract` member of the model.");
            ok = false;
        }

        // R18.1. Roslyn does not put an interface in `BaseType`, so a base-list scan that
        // reads only `BaseType` forgets `class C : IFoo` entirely — the class translated
        // as though the clause were not written, and nothing checked that its members
        // implement anything. §9 has no interfaces (§8.6 says what they wait on), so the
        // clause is refused rather than dropped.
        foreach (var iface in symbol.Interfaces)
        {
            diagnostics.Error("PALCS0594", Locations.From(syntax.Identifier),
                $"`{symbol.Name}` implements `{iface.Name}`, and pal-csharp has no interfaces " +
                "(doc/translation.md R18.2). An interface is nearly R9.2 plus R9.3 — a base with " +
                "no fields whose methods are all abstract — but what a C# interface adds is " +
                "*multiple* implementation, and R9.8 pins the obstacle: a reference is a `dyn` made " +
                "at one witness type, so one value cannot be viewed at two unrelated roots. Use an " +
                "`abstract` base class.");
            ok = false;
        }

        // R9.1. What this class inherits from, and whether the scheme can see it.
        INamedTypeSymbol? baseSymbol = null;
        if (symbol.BaseType is { SpecialType: not SpecialType.System_Object } b
            && b.TypeKind == TypeKind.Class)
        {
            if (!known.HasModel(b))
            {
                diagnostics.Error("PALCS0540", Locations.From(syntax.Identifier),
                    $"`{symbol.Name}` derives from `{b.Name}`, which declares no `[Model]` member and " +
                    "so is not translated. A base class is a model together with a vtable " +
                    "(doc/translation.md R9.5); one with no model has neither.");
                ok = false;
            }
            else if (!b.IsAbstract)
            {
                diagnostics.Error("PALCS0540", Locations.From(syntax.Identifier),
                    $"`{symbol.Name}` derives from `{b.Name}`, which is not `abstract`. A base class " +
                    "supplies a vtable *type*, and a concrete class supplies a vtable *value*; " +
                    "doc/translation.md R9.4 keeps those apart.");
                ok = false;
            }
            else baseSymbol = b;
        }

        // R9.3. Every virtual method is abstract. A `virtual` method with a body would be
        // inherited by a subclass that does not override it, and a base method body can
        // only run against a representation the base does not have. The abstract ones are
        // not collected here: they are ordinary method candidates with no body, so their
        // contracts are bound by the machinery every other method's contract uses.
        foreach (var m in symbol.GetMembers().OfType<IMethodSymbol>()
                     .Where(m => m.MethodKind == MethodKind.Ordinary))
        {
            if (m.IsVirtual && !m.IsAbstract)
            {
                diagnostics.Error("PALCS0542",
                    Locations.From(m.Locations.FirstOrDefault() ?? Location.None),
                    $"`{symbol.Name}.{m.Name}` is `virtual` with a body. A method body runs against a " +
                    "representation, and an abstract class has none (doc/translation.md R9.3), so a " +
                    "subclass that did not override this would have nothing to run. Make it " +
                    "`abstract`, or make it non-virtual and let every subclass share it.");
                ok = false;
            }
        }

        // R9.6. A derived class supplies its parent's model by overriding the parent's
        // [Model] member with an expression over its own. That override *is* the
        // forgetting function, and without it the two models are unrelated.
        ExpressionSyntax? forgetBody = null;
        if (baseSymbol is not null)
        {
            var forget = symbol.GetMembers()
                .FirstOrDefault(m => m.IsOverride && OverriddenChainHasModel(m, known));
            if (forget is null)
            {
                diagnostics.Error("PALCS0543", Locations.From(syntax.Identifier),
                    $"`{symbol.Name}` does not override `{baseSymbol.Name}`'s `[Model]` member. That " +
                    "override is how a subclass says what its parent's model *is* in terms of its own " +
                    "(doc/translation.md R9.6); without it a `" + baseSymbol.Name + "`-typed reference " +
                    $"to a `{symbol.Name}` would have a model nothing could compute.");
                ok = false;
            }
            else if (Body(forget) is not { } fb)
            {
                diagnostics.Error("PALCS0543",
                    Locations.From(forget.Locations.FirstOrDefault() ?? Location.None),
                    $"`{symbol.Name}.{forget.Name}` overrides `{baseSymbol.Name}`'s `[Model]` member " +
                    "but has no expression body. The forgetting function must be a single expression " +
                    "over this class's model.");
                ok = false;
            }
            else forgetBody = fb;
        }

        // R9.2/R9.5: only a class with a representation has an abstraction function.
        ExpressionSyntax? modelBody = null;
        if (!symbol.IsAbstract)
        {
            if (Body(modelSymbol) is not { } concreteBody)
            {
                diagnostics.Error("PALCS0524",
                    Locations.From(modelSymbol.Locations.FirstOrDefault() ?? Location.None),
                    $"`{symbol.Name}`'s `[Model]` member has no expression body. The abstraction function " +
                    "must be a single expression over the fields, because it *is* the connection between " +
                    "the representation and the model.");
                return false;
            }
            modelBody = concreteBody;
        }
        else if (Body(modelSymbol) is not null)
        {
            diagnostics.Error("PALCS0541",
                Locations.From(modelSymbol.Locations.FirstOrDefault() ?? Location.None),
                $"`{symbol.Name}`'s `[Model]` member has an expression body, but `{symbol.Name}` is " +
                "`abstract` and has no fields for it to read (doc/translation.md R9.5). An abstract " +
                "class declares only the model's *type*; each subclass supplies the value.");
            ok = false;
        }

        if (ReturnTypeOf(modelSymbol) is not { } modelReturn)
        {
            diagnostics.Error("PALCS0524",
                Locations.From(modelSymbol.Locations.FirstOrDefault() ?? Location.None),
                $"`{symbol.Name}`'s `[Model]` member has no type.");
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
            observations.ToImmutable(), BuildClassUsings(syntax, symbol))
        {
            BaseSymbol = baseSymbol,
            IsAbstract = symbol.IsAbstract,
            ForgetBody = forgetBody,
        };
        return true;
    }

    /// <summary>
    /// R9.6. Whether an <c>override</c> member overrides — transitively — a member marked
    /// <c>[Model]</c>. C# does not inherit attributes onto an override, so the attribute
    /// is only ever on the original declaration.
    /// </summary>
    private static bool OverriddenChainHasModel(ISymbol member, WellKnown known)
    {
        for (var m = Overridden(member); m is not null; m = Overridden(m))
            if (Declarations.Has(m, known.ModelAttribute)) return true;
        return false;

        static ISymbol? Overridden(ISymbol s) => s switch
        {
            IPropertySymbol p => p.OverriddenProperty,
            IMethodSymbol mm => mm.OverriddenMethod,
            _ => null,
        };
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
                case IrStmtExpr se: Walk(se.Value); return;
                case IrOld o2: Walk(o2.Operand); return;
                case IrLive lv: Walk(lv.Operand); return;
                case IrNewArray na: Walk(na.Length); return;
                case IrContents ct: Walk(ct.Array); return;
                case IrQuantifier q: Walk(q.Body); return;
                case IrCall call: foreach (var a in call.Args) Walk(a); return;
                case IrSeqOp so: foreach (var a in so.Args) Walk(a); return;
                case IrListOp lo: foreach (var a in lo.Args) Walk(a); return;
                case IrSpecOp so: foreach (var a in so.Args) Walk(a); return;
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
                Locations.From(f.Symbol.Locations.FirstOrDefault() ?? Location.None), f.Name, f.Mapped)
            {
                IsBackward = Declarations.Has(f.Symbol, known.BackwardAttribute),
            })
            .ToImmutableArray();

        // R12.1. Everything below this point derives something from the model — the
        // abstraction, the invariant, the observations, the recursion. A `[Plain]` class
        // has no model, so it stops here with just its fields.
        if (c.IsPlain)
            return new IrClass(
                Locations.From(c.Syntax.Identifier), c.Symbol.Name, fields,
                ModelMember: "", ModelType: IrPrim.SpecIntType, ModelBody: null,
                ModelRefinements: [], Invariants: [], Observations: [])
            {
                IsPlain = true,
                TypeParameters = [.. c.Symbol.TypeParameters.Select(t => t.Name)],
            };

        // The abstraction reads the fields; an observation reads the model. Both are
        // written unqualified inside the class, which is the same convention R3.4 uses
        // for a struct's [Refine].
        var fieldNames = c.Fields.Select(f => f.Name).ToImmutableHashSet();
        var modelName = ImmutableHashSet.Create(c.ModelSymbol.Name);

        // R9.2. An abstract class has no abstraction function: there are no fields to
        // abstract from, and each leaf supplies the model instead.
        var modelBody = c.ModelBody is null
            ? null
            : new ExprLowerer(classModel, known, diagnostics, specPosition: true)
              { ClassMembers = fieldNames }.Lower(c.ModelBody);

        // R9.6. The forgetting function reads *this* class's model, exactly as an
        // observation does — it is the base's model written in terms of this one.
        var forgetBody = c.ForgetBody is null
            ? null
            : new ExprLowerer(classModel, known, diagnostics, specPosition: true)
              { ClassMembers = ImmutableHashSet.Create(c.ModelSymbol.Name) }.Lower(c.ForgetBody);

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
            c.ModelSymbol.Name, c.ModelType, modelBody, refinements.ToImmutable(),
            invariants.ToImmutable(), observations)
        {
            BaseClass = c.BaseSymbol?.Name,
            IsAbstract = c.IsAbstract,
            ForgetBody = forgetBody,
            Recursion = Recursion(c, fields, modelBody, known, diagnostics),
            TypeParameters = [.. c.Symbol.TypeParameters.Select(t => t.Name)],
        };
    }

    /// <summary>
    /// R10.5. A class that holds its own nullable type is recursive, and its invariant is
    /// an induction rather than a flat <c>exists*</c>. The user writes no predicate and no
    /// lemma: the induction is read off the <c>[Model]</c> member they already owe, by
    /// inverting the equation <c>M = ctor(… f.M …)</c>. Everything §10 emits is a function
    /// of what this returns, which is why the notation stays this small.
    /// </summary>
    private static IrRecursion? Recursion(
        ClassCandidate c,
        ImmutableArray<IrFieldDecl> fields,
        IrExpr? modelBody,
        WellKnown known,
        DiagnosticBag diagnostics)
    {
        var self = c.Symbol.Name;
        var loc = Locations.From(c.Syntax.Identifier);

        // R10.10. A back pointer is *constrained* by the invariant rather than owned by
        // it. The Pulse shape for that is pinned (test/pulse_facts/RecursiveFacts.fst §8),
        // but the rule that threads the predecessor index through the surface program is
        // not: a freshly allocated node's index is the tail it is about to be linked to,
        // and no general C# rule yet says where that comes from. §0 rule 3 forbids the
        // emitter from inventing one, so the surface refuses rather than guesses.
        foreach (var f in fields.Where(f => f.IsBackward))
        {
            diagnostics.Error("PALCS0566", f.Loc,
                $"`[Backward]` on `{self}.{f.Name}` is not yet translated. The doubly linked " +
                "invariant is pinned in Pulse (doc/translation.md R10.10), but the rule that " +
                "supplies a new node's predecessor index is not, and the emitter may not invent " +
                "one. Use a singly linked field, or write the class in Pulse and import it.");
            return null;
        }
        var recursive = fields
            .Where(f => f.Type is IrClassType { Nullable: true } t && t.Name == self)
            .Select(f => f.Name)
            .ToImmutableHashSet();
        if (recursive.IsEmpty) return null;

        // R10.9. The hierarchy encoding indexes an object by a vtable and reaches it
        // through a `dyn`; the recursive encoding indexes it by its own model and reaches
        // it through an `option`. Nothing has probed the two at once.
        if (c.IsAbstract || c.BaseSymbol is not null)
        {
            diagnostics.Error("PALCS0565", loc,
                $"`{self}` holds a field of its own type *and* takes part in a class hierarchy. " +
                "The recursive encoding (doc/translation.md R10.3) and the hierarchy encoding (R9.9) " +
                "index an object in different ways and have not been shown to compose. Make the " +
                "recursive class `sealed` and free-standing.");
            return null;
        }

        // R10.6. A recursive class's invariant recurses into the sub-model, so every other
        // field must be a value the cons case can state purely. An array or a *different*
        // object would each contribute their own ownership at every node, which the case
        // lemmas would then have to thread — not probed.
        foreach (var f in fields)
        {
            if (f.Type is IrClassType { Nullable: true } t && t.Name == self) continue;
            // R15.5. A type parameter is such a value: unconstrained, it carries no
            // ownership of its own, so the cons case states it as an equation on the
            // model and the induction is unaffected.
            if (f.Type is IrPrim or IrNamedType or IrTypeParamType) continue;
            diagnostics.Error("PALCS0563", f.Loc,
                $"`{self}.{f.Name}` has type `{f.Type}`, but `{self}` is recursive: it holds a field " +
                "of its own type. A recursive class's invariant is an induction on its model " +
                "(doc/translation.md R10.3), and every other field must be a value that induction can " +
                "state purely. Hold the array or object in a non-recursive class instead.");
            return null;
        }

        // R11.5. The model's two constructors, as F* names. There is no enum of built-in
        // shapes any more: a model type is a type with an empty constructor and a
        // non-empty one, and where those names come from — the compiler, for `SpecList`,
        // or the user's `[SpecCtor]`, for anything else — changes nothing downstream.
        //
        // R10.5. The body must be a *single* application of the non-empty constructor.
        // That is not a syntactic convenience: the emitter inverts it to get the
        // invariant, and an equation it cannot invert is one whose induction does not
        // exist, so guessing one would be inventing a proof step (§0 rule 3).
        //
        // F44 is why the built-in arm can say `Nil` and `Cons` rather than `[]` and `::`:
        // they are the same constructors, and the prefix form works in every position,
        // which is what lets one template serve a built-in model type and a user's alike.
        var (shape, args) = (c.ModelType, modelBody) switch
        {
            (IrSpecListType, IrListOp { Op: ListOpKind.Cons } l) =>
                (new IrModelShape("Nil", "Cons"), l.Args),
            (IrUserSpecType, IrSpecOp { SiblingEmpty: { } empty } o) =>
                (new IrModelShape(empty, o.Function), o.Args),
            _ => (null, default(ImmutableArray<IrExpr>)),
        };

        if (shape is null)
        {
            // Which of the two things went wrong: the model's *type* cannot be inducted
            // over at all, or it can but the body is not one application of its
            // constructor. Separating them is what makes each message actionable.
            if (c.ModelType is not (IrSpecListType or IrUserSpecType))
            {
                diagnostics.Error("PALCS0560",
                    Locations.From(c.ModelSymbol.Locations.FirstOrDefault() ?? Location.None),
                    $"`{self}` is recursive, so its model must be an inductive type whose empty " +
                    $"constructor is what a null reference denotes. `{c.ModelType}` is not one: use " +
                    "`SpecList<T>`, `SpecTree<T>`, or a type of your own declared with " +
                    "`[SpecType]` and `[SpecCtor]` (doc/translation.md R11.1).");
                return null;
            }

            // R11.3. A user's type whose constructors do not say which one is empty. A
            // null reference has to denote exactly one thing, and nothing else in the
            // program says which.
            if (c.ModelType is IrUserSpecType u && modelBody is IrSpecOp { SiblingEmpty: null })
            {
                diagnostics.Error("PALCS0572",
                    Locations.From(c.ModelBody?.GetLocation() ?? Location.None),
                    $"`{u.Name}` is used as the model of the recursive class `{self}`, but none of " +
                    "its constructors is marked `[SpecCtor(..., Empty = true)]`. That is the " +
                    "constructor a null reference denotes, and so the base case of the induction " +
                    "(doc/translation.md R11.3).");
                return null;
            }

            diagnostics.Error("PALCS0561",
                Locations.From(c.ModelBody?.GetLocation() ?? Location.None),
                $"The `[Model]` of the recursive class `{self}` must be exactly one application of " +
                $"a constructor of `{c.ModelType}`, whose recursive arguments are the sub-models " +
                $"`f.{c.ModelSymbol.Name}` of its own fields. The translator inverts that equation " +
                "to obtain the class's inductive ownership predicate (doc/translation.md R10.5), " +
                "and cannot invert anything else.");
            return null;
        }

        var used = ImmutableHashSet<string>.Empty;
        var lowered = ImmutableArray.CreateBuilder<IrRecArg>();
        foreach (var arg in args)
        {
            if (arg is IrVar v && recursive.Contains(v.Name))
            {
                used = used.Add(v.Name);
                lowered.Add(new IrRecField(v.Name));
                continue;
            }
            lowered.Add(new IrRecPure(arg));
        }

        // Every recursive field must appear, exactly once. A field the model never
        // mentions is memory the invariant would have to own with nothing to own it at,
        // and a field mentioned twice would be owned twice.
        foreach (var f in recursive)
            if (!used.Contains(f))
            {
                diagnostics.Error("PALCS0562", loc,
                    $"`{self}.{f}` is a field of `{self}`'s own type, but the `[Model]` member " +
                    $"`{c.ModelSymbol.Name}` does not use it as `{f}.{c.ModelSymbol.Name}`. The " +
                    "recursion of the invariant is read off the recursion of the model " +
                    "(doc/translation.md R10.5), so a field the model does not reach is memory the " +
                    "invariant cannot own.");
                return null;
            }
        if (used.Count != lowered.OfType<IrRecField>().Count())
        {
            diagnostics.Error("PALCS0562", loc,
                $"The `[Model]` of `{self}` uses one of its recursive fields more than once. Each " +
                "occurrence would own that sub-object again (doc/translation.md R10.5).");
            return null;
        }

        return new IrRecursion(shape, lowered.ToImmutable(), null);
    }

    /// <summary>R12.1. Whether a type is a <c>[Plain]</c> class.</summary>
    private static bool IsPlainClass(ITypeSymbol? t, WellKnown known) =>
        (t as INamedTypeSymbol)?.OriginalDefinition is { } n &&
        Declarations.Has(n, known.PlainAttribute);

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
            // R15.1. `using static` names a *closed* type, so a generic helper type
            // cannot be imported. Nothing is lost: what the import buys is unqualified
            // access to a *static* helper, and a [Spec] member of a generic class is
            // reached through a receiver whose type supplies the arguments anyway.
            .Where(t => t.TypeParameters.Length == 0)
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
                    Usings: usings)
                {
                    TypeParameters = MethodTypeParameters(candidate.Symbol),
                });
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

        // R15.1. A generic declaring type cannot be `using static`-imported: the
        // directive names a closed type and there is nothing to close it with. The
        // members it would have imported are reached through a receiver instead.
        var own = candidate.Symbol.ContainingType.TypeParameters.Length > 0
            ? null
            : $"using static {candidate.Symbol.ContainingType.ToDisplayString(SymbolDisplayFormat.FullyQualifiedFormat)};";

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
            .. own is null || helperTypes.Contains(own) ? ImmutableArray<string>.Empty : [own],
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

    /// <summary>
    /// R15 refusals for type declarations. M9 translates a generic class or struct that
    /// stands alone; the cases below are the ones whose translation is not designed.
    /// </summary>
    private static bool RefuseGenericType(INamedTypeSymbol symbol, DiagnosticBag diagnostics)
    {
        var loc = Locations.From(symbol.Locations.FirstOrDefault() ?? Location.None);

        // A generic base is refused at the derived class as well as at the base, so that
        // no hierarchy anywhere contains a parameterised class.
        if (symbol.BaseType is { SpecialType: not SpecialType.System_Object } derivedBase &&
            derivedBase.TypeParameters.Length > 0)
        {
            diagnostics.Error("PALCS0581", loc,
                $"`{symbol.Name}` derives from the generic class `{derivedBase.Name}`. " +
                "pal-csharp translates a generic class that stands alone (doc/translation.md " +
                "R15.1): the vtable and the cast lemmas of a parameterised hierarchy have not " +
                "been designed. Write the base at a concrete element type.");
            return true;
        }

        if (symbol.TypeParameters.Length == 0) return false;

        // R14.1, restated for a type: a constraint is a typeclass obligation the scheme
        // does not carry, at a method and equally at the type that declares the parameter.
        foreach (var tp in symbol.TypeParameters)
        {
            if (WellKnown.Unconstrained(tp)) continue;
            diagnostics.Error("PALCS0580", Locations.From(
                    tp.Locations.FirstOrDefault() ?? symbol.Locations.FirstOrDefault() ?? Location.None),
                $"The type parameter `{tp.Name}` of `{symbol.Name}` is constrained. " +
                "pal-csharp translates unconstrained type parameters (doc/translation.md R14.1): " +
                "a constraint is a typeclass obligation, and the dictionary a call through it " +
                "would need has not been designed. Drop the constraint, or write the type at " +
                "the concrete type you need.");
            return true;
        }

        // R15.1. A generic `struct` is a *value*: it is copied at every assignment and
        // stored inline in whatever holds it, and §8's representation is a record, not a
        // reference with an invariant. Parameterising that record is not the same problem
        // as parameterising a class and has not been designed, so it is refused here
        // rather than translated by analogy.
        if (symbol.TypeKind == TypeKind.Struct)
        {
            diagnostics.Error("PALCS0581", loc,
                $"`{symbol.Name}` is a generic struct. pal-csharp translates a generic class " +
                "(doc/translation.md R15.1): a struct is a value, copied at every assignment " +
                "and stored inline, and its representation record has not been designed with " +
                "a type parameter. Write the struct at the element type you need, or make it " +
                "a class.");
            return true;
        }

        // R15.1. A parameterised hierarchy would need a parameterised vtable, and the
        // cast lemmas that relate a derived record to its base would have to be
        // parameterised alongside it. Neither is designed, so M9 refuses the case rather
        // than emitting a vtable whose type arguments do not line up.
        if (symbol.IsAbstract ||
            symbol.BaseType is { SpecialType: not SpecialType.System_Object })
        {
            diagnostics.Error("PALCS0581", loc,
                $"`{symbol.Name}` is a generic class that participates in a hierarchy. " +
                "pal-csharp translates a generic class that stands alone (doc/translation.md " +
                "R15.1): the vtable and the cast lemmas of a parameterised hierarchy have not " +
                "been designed. Make the class sealed and standalone, or write it at a " +
                "concrete element type.");
            return true;
        }

        // R15.4. C# guarantees that a *direct* recursive occurrence is at the same
        // arguments only when they are the declaring parameters themselves; `Nest<T>`
        // with a `Nest<(T, T)>` field is legal C# and would need a non-uniform (and in
        // F* an inductive-inductive) definition. Refused rather than mistranslated.
        foreach (var field in symbol.GetMembers().OfType<IFieldSymbol>())
        {
            if (field.IsStatic || field.IsImplicitlyDeclared) continue;
            if (!UniformlyRecursive(field.Type, symbol))
            {
                diagnostics.Error("PALCS0582", Locations.From(
                        field.Locations.FirstOrDefault() ?? symbol.Locations.FirstOrDefault() ?? Location.None),
                    $"The field `{field.Name}` makes `{symbol.Name}` non-uniformly recursive: it " +
                    "mentions the declaring type at type arguments other than the declaring " +
                    "type parameters. pal-csharp translates uniform recursion " +
                    "(doc/translation.md R15.4): a type whose recursive occurrences change " +
                    "their arguments is not an F* inductive. Write the field at the declaring " +
                    "type parameters.");
                return true;
            }
        }

        return false;
    }

    /// <summary>
    /// R15.4. Whether every occurrence of <paramref name="decl"/> inside
    /// <paramref name="type"/> is at exactly <paramref name="decl"/>'s own type
    /// parameters, in order.
    /// </summary>
    private static bool UniformlyRecursive(ITypeSymbol type, INamedTypeSymbol decl)
    {
        if (type is IArrayTypeSymbol array) return UniformlyRecursive(array.ElementType, decl);
        if (type is not INamedTypeSymbol named) return true;

        if (SymbolEqualityComparer.Default.Equals(named.OriginalDefinition, decl.OriginalDefinition))
        {
            if (named.TypeArguments.Length != decl.TypeParameters.Length) return false;
            for (var i = 0; i < named.TypeArguments.Length; i++)
            {
                if (!SymbolEqualityComparer.Default.Equals(
                        named.TypeArguments[i], decl.TypeParameters[i]))
                    return false;
            }
        }

        foreach (var arg in named.TypeArguments)
        {
            if (SymbolEqualityComparer.Default.Equals(arg.OriginalDefinition, decl.OriginalDefinition) &&
                !UniformlyRecursive(arg, decl))
                return false;
            if (arg is INamedTypeSymbol { TypeArguments.Length: > 0 } && !UniformlyRecursive(arg, decl))
                return false;
        }
        return true;
    }

    /// <summary>
    /// R15.1. A method's binders are its declaring type's type parameters followed by its
    /// own: a method of `Node&lt;T&gt;` mentions `T` in its signature exactly as a generic
    /// method mentions the parameter it declares itself, and the two are bound the same way.
    /// </summary>
    private static ImmutableArray<string> MethodTypeParameters(IMethodSymbol symbol) =>
    [
        .. symbol.ContainingType?.TypeParameters.Select(t => t.Name) ?? [],
        .. symbol.TypeParameters.Select(t => t.Name),
    ];

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
            // R15.3. The receiver of a method of `Node<T>` is a `Node<T>`, not a `Node`.
            parameters = [new IrParam(loc, Names.This,
                              known.MapType(self) ?? new IrClassType(self.Name), ParamMode.Value),
                          .. parameters];
        }

        if (candidate.Kind == CalleeKind.Spec)
            return LowerSpecFunction(candidate, model, known, diagnostics, loc, parameters, specs);

        var returnType = symbol.MethodKind == MethodKind.Constructor
            ? known.MapType(symbol.ContainingType) ?? new IrClassType(symbol.ContainingType.Name)
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

        // R14.1. A constraint is a typeclass obligation the scheme does not carry, so a
        // constrained type parameter is refused here rather than translated with the
        // constraint dropped -- which would admit a program whose body cannot be written.
        foreach (var tp in symbol.TypeParameters)
        {
            if (WellKnown.Unconstrained(tp)) continue;
            diagnostics.Error("PALCS0580", Locations.From(
                    tp.Locations.FirstOrDefault() ?? symbol.Locations.FirstOrDefault() ?? Location.None),
                $"The type parameter `{tp.Name}` of `{symbol.Name}` is constrained. " +
                "pal-csharp translates unconstrained type parameters (doc/translation.md R14.1): " +
                "a constraint is a typeclass obligation, and the dictionary a call through it " +
                "would need has not been designed. Drop the constraint, or write the method at " +
                "the concrete type you need.");
            return null;
        }

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
            // R4.11b derives this from the write set. R9.7: an abstract method has no
            // write set, so [Frac] on the method says it instead — the same statement
            // R4.9a makes about a parameter, made about the receiver.
            IsReadOnly = declaringClass is not null &&
                symbol.MethodKind != MethodKind.Constructor &&
                (Declarations.Has(symbol, known.FracAttribute) ||
                 (!symbol.IsAbstract && !Declarations.Mutates(candidate.Syntax, model))),
            IsAbstract = symbol.IsAbstract,
            // R14.2. Type parameters become binders ahead of every value parameter. The
            // constrained case never reaches here: MapType declines a constrained type
            // parameter, so the signature that mentions it is refused first.
            TypeParameters = MethodTypeParameters(symbol),
            Overrides = symbol is { IsOverride: true, ContainingType.BaseType.Name: { } baseName }
                ? baseName
                : null,
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
            TypeParameters = MethodTypeParameters(candidate.Symbol),
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
                // R12.1. A parameter is plain either because it says so, or because its
                // *class* does: a `[Plain]` class has no derived invariant to own it
                // through, so every reference to one carries the resource its contract
                // names and nothing implicit.
                Plain = Declarations.Has(p, known.PlainAttribute) ||
                        IsPlainClass(declared, known),
                // R17.2. A `ReadOnlySpan<T>` is fractional whether or not `[Frac]` is
                // written. The C# type already says read-only, so asking the author to
                // repeat it in an attribute would be the translator demanding to be told
                // something the program states -- §0 rule 3 in the "never invent a refusal"
                // direction. An explicit `[Frac("p")]` still wins, because naming the
                // permission is how two parameters are made to share one array (R4.9).
                Fraction = Declarations.Find(p, known.FracAttribute) is { } f
                    ? Declarations.StringArgument(f)
                    : known.IsReadOnlySpan(declared) ? "p_" + p.Name : null,
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
