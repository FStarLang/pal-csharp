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
public static partial class FrontendPass
{
    public static IrProgram Run(CSharpCompilation compilation, DiagnosticBag diagnostics)
    {
        var known = WellKnown.For(compilation);
        ValidateSpecTypes(compilation, known, diagnostics);
        var candidates = Collect(compilation, known, diagnostics);
        var structs = CollectStructs(compilation, known, diagnostics);
        var attempted = ImmutableHashSet.CreateBuilder<ISymbol>(SymbolEqualityComparer.Default);
        var classes = CollectClasses(compilation, known, diagnostics, attempted);
        ReportUncollected(compilation, known, classes, attempted.ToImmutable(), diagnostics);
        var sites = BuildSpecSites(compilation, known, candidates)
            .AddRange(BuildStructSpecSites(structs))
            .AddRange(BuildClassSpecSites(classes));

        var bound = SpecBinder.Bind(ref compilation, sites, diagnostics);

        var declarations = ImmutableArray.CreateBuilder<IrDecl>();
        declarations.AddRange(CollectExceptions(compilation, known, diagnostics));
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
            var lifted = new List<IrMethod>();
            var decl = LowerDeclaration(candidate, model, known, bound, diagnostics, lifted);
            if (decl is not null) declarations.Add(decl);
            if (decl is IrMethod enclosing)
                declarations.AddRange(lifted.Select(l => l with { RlimitFactor = enclosing.RlimitFactor }));
        }

        // R27.57. The replicas the bodies asked for, each a base body verified again at a
        // representation-sharing subclass; a replica's own calls may ask for more.
        Subclasses.Check(candidates.Select(c => (c.Syntax, c.Symbol)), compilation, known, diagnostics);
        while (known.ReplicaDemand.Count > 0)
        {
            var request = known.ReplicaDemand.Dequeue();
            var source = candidates.FirstOrDefault(c => Naming.Of(c.Symbol) == request.Source);
            if (source is null)
            {
                diagnostics.Error("PALCS0715", Locations.From(request.At.Locations.FirstOrDefault() ?? Location.None),
                    $"`{request.Source}` would have to be verified again at `{request.At.Name}`, whose override it " +
                    "reaches, but it is not translated (doc/translation.md R27.57).");
                continue;
            }
            var model = compilation.GetSemanticModel(source.Syntax.SyntaxTree);
            var lifted = new List<IrMethod>();
            known.Replica = request;
            var decl = LowerDeclaration(source, model, known, bound, diagnostics, lifted);
            known.Replica = null;
            if (decl is not IrMethod replica) continue;
            declarations.Add(replica with
            {
                Name = request.Name,
                Throws = [.. replica.Throws, .. replica.AtThrows.Where(t => t.At == request.At.Name).Select(t => t.Throws)],
                AtThrows = [],
            });
            declarations.AddRange(lifted.Select(l => l with { RlimitFactor = replica.RlimitFactor }));
        }

        foreach (var include in CollectIncludes(compilation, known, diagnostics))
            declarations.Add(include);

        // R9.21. The split runs before contracts are inherited, so the `abstract`
        // declaration it creates is the one `InheritContracts` reads the contract from —
        // exactly as if the user had written the two halves out.
        OpenClasses.Desugar(declarations);
        InheritContracts(declarations, diagnostics);
        PropagateDefaults(declarations);
        return new IrProgram(declarations.ToImmutable());
    }

    /// <summary>
    /// R22.22. A method that calls one needing <c>has_default</c> at a type parameter
    /// needs it too, at whatever of its own type parameters it passes there: the
    /// instance is resolved at the call, from the caller's binders. Iterated to a fixed
    /// point, because the need travels up any chain of calls.
    /// </summary>
    private static void PropagateDefaults(ImmutableArray<IrDecl>.Builder declarations)
    {
        bool changed;
        do
        {
            changed = false;
            var byName = declarations.OfType<IrMethod>().GroupBy(m => m.Name)
                .ToDictionary(g => g.Key, g => g.First());
            for (var i = 0; i < declarations.Count; i++)
            {
                if (declarations[i] is not IrMethod { Body: { } body } m) continue;
                var needed = new HashSet<string>(m.DefaultedTypeParameters);
                foreach (var call in Passes.Check.Statements(body).SelectMany(Passes.Check.Expressions)
                             .SelectMany(Passes.Check.Subexpressions).OfType<IrCall>())
                {
                    if (!byName.TryGetValue(call.Callee, out var callee)) continue;
                    foreach (var tp in callee.DefaultedTypeParameters)
                    {
                        var k = callee.TypeParameters.IndexOf(tp);
                        if (k >= 0 && k < call.TypeArguments.Length)
                            foreach (var name in DefaultedIn(call.TypeArguments[k]))
                                if (m.TypeParameters.Contains(name))
                                    needed.Add(name);
                    }
                }
                if (needed.Count == m.DefaultedTypeParameters.Length) continue;
                declarations[i] = m with
                {
                    DefaultedTypeParameters = [.. m.TypeParameters.Where(needed.Contains)],
                };
                changed = true;
            }
        } while (changed);
    }

    // R22.22. The type parameters a `has_default` instance at `t` is resolved from: `t`
    // itself, or those of a tuple's or a struct's arguments (their instances are built
    // from their components').
    private static IEnumerable<string> DefaultedIn(IrType t) => t switch
    {
        IrTypeParamType p => [p.Name],
        IrUserSpecType u => u.Args.SelectMany(DefaultedIn),
        IrNamedType n => n.TypeArguments.SelectMany(DefaultedIn),
        _ => [],
    };

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
        // Grouped, not added: see SpecBinder. A duplicate here is R2.1a's to prevent and
        // PALCS0501's to report, and neither is served by throwing.
        var byName = declarations.OfType<IrMethod>()
            .Where(m => m.IsAbstract && m.DeclaringClass is not null)
            .GroupBy(m => m.Name)
            .ToDictionary(g => g.Key, g => g.First());
        // R9.18. `Overrides` names the *immediate* base, because that is the class whose
        // model the override's vtable slot is typed at. It is not necessarily the class
        // that *declared* the method: at depth three `Square.GetArea` overrides through
        // `Quadrilateral`, which declares no `GetArea` of its own. So the contract is
        // looked up by walking, and the two questions — whose model, and whose contract —
        // are answered separately, which is what they always were.
        var bases = declarations.OfType<IrClass>()
            .Where(c => c.BaseClass is not null)
            .GroupBy(c => c.Name)
            .ToDictionary(g => g.Key, g => g.First().BaseClass!);

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

    /// <remarks>
    /// R9.20 widens <c>Syntax</c> from a method declaration to any declaration a
    /// translated body can be written in, because a computed property is a body the user
    /// wrote and C# does not spell it as a method. The property carries the attributes and
    /// the accessor carries the body, so the two are one candidate: <c>Symbol</c> is the
    /// accessor (its parameters and return type are the method's) and <c>Declaration</c>
    /// is the property (its attributes are the contract, and its name is the module's).
    /// </remarks>
    private sealed record Candidate(
        SyntaxNode Syntax,
        IMethodSymbol Symbol,
        CalleeKind Kind)
    {
        /// <summary>The name token: a method's identifier, a constructor's type name, or
        /// a property's name — never the accessor's, which the user did not write.</summary>
        public SyntaxToken Identifier => Syntax switch
        {
            MethodDeclarationSyntax m => m.Identifier,
            ConstructorDeclarationSyntax c => c.Identifier,
            PropertyDeclarationSyntax p => p.Identifier,
            IndexerDeclarationSyntax ix => ix.ThisKeyword,
            AccessorDeclarationSyntax { Parent.Parent: IndexerDeclarationSyntax ix } => ix.ThisKeyword,
            AccessorDeclarationSyntax { Parent.Parent: PropertyDeclarationSyntax p } => p.Identifier,
            _ => Syntax.GetFirstToken(),
        };

        public ArrowExpressionClauseSyntax? ExpressionBody => Syntax switch
        {
            MethodDeclarationSyntax m => m.ExpressionBody,
            ConstructorDeclarationSyntax c => c.ExpressionBody,
            // `T P => e;` and `T P { get => e; }` are the same declaration with the same
            // body; the accessor form is where an attribute could never have gone.
            PropertyDeclarationSyntax p => p.ExpressionBody ?? Getter(p)?.ExpressionBody,
            IndexerDeclarationSyntax ix => ix.ExpressionBody,
            AccessorDeclarationSyntax a => a.ExpressionBody,
            _ => null,
        };

        /// <summary>The declaration the contract is read from: R9.20c's property, or the
        /// method itself — which for a property is its getter when the attributes are
        /// written on the <c>get</c>.</summary>
        public ISymbol Declaration => ContractOverride ??
            (Syntax is IndexerDeclarationSyntax && Symbol.AssociatedSymbol is { } ixp ? ixp :
            Syntax is PropertyDeclarationSyntax pd && Symbol.AssociatedSymbol is { } p &&
            !(Getter(pd) is { } g && g.AttributeLists.SelectMany(l => l.Attributes).Any(IsContractAttribute)) ? p : Symbol);

        /// <summary>R27.12. The `get` accessor, when the contract was written there.</summary>
        public ISymbol? ContractOverride { get; init; }

        private static bool IsContractAttribute(AttributeSyntax a) =>
            a.Name.ToString().Split('.')[^1].Replace("Attribute", "") is
                "Requires" or "Ensures" or "Preserves" or "PreservesValue" or "Throws" or "Decreases";

        public static AccessorDeclarationSyntax? Getter(PropertyDeclarationSyntax p) =>
            p.AccessorList?.Accessors.FirstOrDefault(
                a => a.Kind() == SyntaxKind.GetAccessorDeclaration);
    }

    /// <summary>
    /// R27.12. A computed property's contract may be written on the property or on its
    /// `get` accessor, but not on both: the accessor is the contract's source exactly when
    /// it carries one.
    /// </summary>
    private static ISymbol? AccessorContract(
        IPropertySymbol property, IMethodSymbol getter, WellKnown known, DiagnosticBag diagnostics)
    {
        bool HasContract(ISymbol s) =>
            SpecAttributes(s, known).Any() || ThrowsAttributes(s, known).Any();
        if (!HasContract(getter)) return null;
        if (HasContract(property))
        {
            diagnostics.Error("PALCS0704",
                Locations.From(getter.Locations.FirstOrDefault() ?? Location.None),
                $"`{property.Name}` has a contract on both the property and its `get` accessor. " +
                "Write it in one place (doc/translation.md R27.12).");
            return null;
        }
        return getter;
    }

    private static ImmutableArray<Candidate> Collect(CSharpCompilation compilation, WellKnown known, DiagnosticBag diagnostics)
    {
        var result = ImmutableArray.CreateBuilder<Candidate>();
        foreach (var tree in compilation.SyntaxTrees)
        {
            var model = compilation.GetSemanticModel(tree);
            foreach (var method in tree.GetRoot().DescendantNodes().OfType<BaseMethodDeclarationSyntax>())
            {
                if (model.GetDeclaredSymbol(method) is not IMethodSymbol symbol) continue;
                // R11.1a. A specification type's members declare F* names; they are not
                // executable code and have no bodies to translate.
                if (known.IsSpecTypeDeclaration(symbol.ContainingType)) continue;
                if (Declarations.KindOf(symbol, known) is not { } kind) continue;
                result.Add(new Candidate(method, symbol, kind));
            }

            // R9.20. A computed property is the method its getter is. It is collected here
            // rather than beside the fields, because everything downstream of this point
            // treats it as a method and nothing downstream needs to know it was written as
            // a property.
            foreach (var prop in tree.GetRoot().DescendantNodes().OfType<PropertyDeclarationSyntax>())
            {
                if (model.GetDeclaredSymbol(prop) is not IPropertySymbol symbol) continue;
                if (known.IsSpecTypeDeclaration(symbol.ContainingType)) continue;
                if (!IsComputed(symbol, known)) continue;
                if (symbol.GetMethod is not { } getter) continue;
                if (Declarations.KindOf(getter, known) is not { } kind) continue;
                result.Add(new Candidate(prop, getter, kind)
                    { ContractOverride = AccessorContract(symbol, getter, known, diagnostics) });
            }

            // R22.13. A property's setter is the method `set_P(value)`, collected from its
            // accessor, which is where its body and its contract are written. So is the
            // getter of a property that has a setter too, which R9.20 does not collect.
            foreach (var prop in tree.GetRoot().DescendantNodes().OfType<PropertyDeclarationSyntax>())
            {
                if (prop.AccessorList is null) continue;
                foreach (var accessor in prop.AccessorList.Accessors)
                {
                    if (!accessor.IsKind(SyntaxKind.SetAccessorDeclaration) &&
                        !accessor.IsKind(SyntaxKind.GetAccessorDeclaration)) continue;
                    if (accessor.IsKind(SyntaxKind.GetAccessorDeclaration) &&
                        (model.GetDeclaredSymbol(prop) is not IPropertySymbol { SetMethod: not null } ps ||
                         IsAuto(ps)))
                        continue;
                    if (accessor.Body is null && accessor.ExpressionBody is null) continue;
                    if (model.GetDeclaredSymbol(accessor) is not IMethodSymbol setter) continue;
                    if (known.IsSpecTypeDeclaration(setter.ContainingType)) continue;
                    if (Declarations.KindOf(setter, known) is not { } kind) continue;
                    result.Add(new Candidate(accessor, setter, kind));
                }
            }

            // R22.13. An indexer accessor is the method C# compiles it to (`get_Item`,
            // `set_Item`), and its contract is written on the accessor: the two accessors
            // are two methods with two contracts, and an attribute on the indexer itself
            // could not say which one it meant.
            foreach (var ix in tree.GetRoot().DescendantNodes().OfType<IndexerDeclarationSyntax>())
            {
                // R33.13. `T this[int i] => e;` has no accessor to write the contract on, so
                // it is written on the indexer, as R9.20 has it for `T P => e;`.
                if (ix is { AccessorList: null, ExpressionBody: not null })
                {
                    if (model.GetDeclaredSymbol(ix) is not IPropertySymbol { GetMethod: { } g } ip) continue;
                    if (known.IsSpecTypeDeclaration(ip.ContainingType)) continue;
                    if (Declarations.KindOf(g, known) is not { } gk) continue;
                    result.Add(new Candidate(ix, g, gk));
                    continue;
                }
                if (ix.AccessorList is null) continue;
                foreach (var accessor in ix.AccessorList.Accessors)
                {
                    if (model.GetDeclaredSymbol(accessor) is not IMethodSymbol symbol) continue;
                    if (known.IsSpecTypeDeclaration(symbol.ContainingType)) continue;
                    if (Declarations.KindOf(symbol, known) is not { } kind) continue;
                    result.Add(new Candidate(accessor, symbol, kind));
                }
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
                // R29.3. A borrowing class's members are translated with it as a record.
                if (Borrowing.IsBorrowingClass(owner, known)) continue;

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
        TypeDeclarationSyntax Syntax,
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

                    // R29.4. Nor does a static one producing an `object`: it reads no
                    // specification type, and an `obj` is no type's to own.
                    var producesObject = member.IsStatic && WellKnown.IsObjectLike(member switch
                    {
                        IMethodSymbol om => om.ReturnType,
                        IPropertySymbol op => op.Type,
                        IFieldSymbol of => of.Type,
                        _ => null,
                    });

                    // R30.5. Nor does a static method of a static class bound by R21.5: a
                    // helper such as `HashHelpers.GetPrime` reads nothing but its arguments,
                    // like a method of a class outside the sources (`BitOperations.Log2`).
                    var staticHelper = member is IMethodSymbol { IsStatic: true } && type.IsStatic &&
                        known.SpecTypeName(type) is null;

                    // R27.58. A nested class bound by R21.5 is a type, not an operation.
                    if (member is not ITypeSymbol &&
                        known.SpecOpName(member) is not null && known.SpecTypeName(type) is null &&
                        !isPredicate && !producesObject && !staticHelper &&
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
            foreach (var syntax in tree.GetRoot().DescendantNodes().OfType<TypeDeclarationSyntax>())
            {
                if (syntax is not (StructDeclarationSyntax or ClassDeclarationSyntax)) continue;
                if (model.GetDeclaredSymbol(syntax) is not { } symbol) continue;
                // R29.3. A borrowing class is represented by the record of its fields.
                if (syntax is ClassDeclarationSyntax && !Borrowing.IsBorrowingClass(symbol, known)) continue;
                if (Declarations.Has(symbol, known.PulseTypeAttribute)) continue;
                if (known.IsSpecTypeDeclaration(symbol)) continue;   // R11.1a
                // R20.1. Under `[TranslateAnnotatedOnly]` a struct is translated only when it
                // or one of its members says so.
                // R24.6. A struct nested in a class with a model, held by one of its
                // fields, is that class's representation and is translated with it.
                if (known.AnnotatedOnly && !Declarations.IsAnnotated(symbol, known) &&
                    !symbol.GetMembers().Any(m => Declarations.IsAnnotated(m, known)) &&
                    !(symbol.ContainingType is { } owner && known.HasModel(owner) &&
                      owner.GetMembers().OfType<IFieldSymbol>().Any(f => !f.IsStatic &&
                          SymbolEqualityComparer.Default.Equals(
                              (f.Type is IArrayTypeSymbol at ? at.ElementType : f.Type).OriginalDefinition,
                              symbol.OriginalDefinition)))) continue;
                // R22.6. A `[Spec]` struct is an erased record, never copied or stored at run
                // time, so R15.1's reason for refusing a generic struct does not apply to it.
                if (!(Declarations.Has(symbol, known.SpecAttribute) && symbol.TypeParameters.All(WellKnown.Unconstrained))
                    && !Borrowing.IsView(symbol, known)   // R32.13
                    && RefuseGenericType(symbol, diagnostics)) continue;

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

                // R32.13. A view's record also holds the state it inherits.
                foreach (var member in symbol.GetMembers().Concat(Borrowing.InheritedState(symbol, known)))
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
                    // R28.1. The one readonly field typed at an enclosing class is a
                    // borrowed reference: the record holds the box and owns nothing.
                    var borrowed = mapped is IrClassType &&
                        SymbolEqualityComparer.Default.Equals(Borrowing.OwnerField(symbol, known), member);
                    // R27.37. A borrowing struct may also hold an object it owns (the record
                    // holds the box; its members take the object's invariant alongside) and a
                    // pointer into the borrowed object's region (a value, R27.3).
                    borrowed |= mapped is IrClassType && Borrowing.IsBorrowing(symbol, known) &&
                        (known.IsRegionClass(type) ||
                         member is IFieldSymbol of && Borrowing.OwnedFields(symbol, known).Contains(of, SymbolEqualityComparer.Default));
                    // R32.10. A spec-only struct may hold a pointer into a region: a value
                    // that owns nothing, which names nodes of the region's heap.
                    borrowed |= specOnly && mapped is IrClassType && known.IsRegionClass(type);
                    // R32.13. A view holds its base's comparer, a pure value (R27.47).
                    borrowed |= mapped is not null && Sorted.IsComparer(mapped) && Borrowing.IsView(symbol, known);
                    if (mapped is null || !(borrowed || (specOnly ? IsSpecField(mapped) : IsValueField(mapped))))
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

    /// <summary>
    /// R9.20: a property whose accessor has a body, over the representation. Not an
    /// auto-property (R3.4 reads that as a field), not a <c>[Model]</c> or a <c>[Spec]</c>
    /// observation (R3.9c reads those off the model), and read-only, per R9.20b.
    /// </summary>
    private static bool IsComputed(IPropertySymbol p, WellKnown known) =>
        p is { IsStatic: false, IsIndexer: false, GetMethod: not null, SetMethod: null }
        // R29.3b. A `field ??= new V(this)` getter caches a view; its backing field is in
        // no representation, and the getter is the method its body is.
        && (!IsAuto(p) || p.ContainingType.GetMembers().OfType<IFieldSymbol>().Any(f =>
                SymbolEqualityComparer.Default.Equals(f.AssociatedSymbol, p) && Borrowing.IsBorrowingClass(f.Type, known)))
        && !Declarations.IsAnnotatedDeclaration(p, known)
        // R9.6's forgetting function is written as `override SpecInt Area => ...`, and
        // carries no attribute of its own: it inherits its meaning from the `[Model]` it
        // overrides. It is a spec-level definition, not code over the representation, so
        // reading it as a method would translate a specification as a program.
        && !(p.IsOverride && OverriddenChainHasModel(p, known))
        && (p.ContainingType is { TypeKind: TypeKind.Class } owner &&
               (known.HasModel(owner) || known.IsRegionClass(owner))
            // R28.2. A borrowing struct's getter is a member of the borrowed object's class.
            // R29.4. An explicit one (`object IEnumerator.Current`) when it carries a contract.
            || (Borrowing.IsBorrowing(p.ContainingType, known) || Borrowing.IsWrapping(p.ContainingType, known)) &&
               (p.ExplicitInterfaceImplementations.IsEmpty || Declarations.IsAnnotated(p, known)));

    private static bool IsAuto(IPropertySymbol p) =>
        p.ContainingType.GetMembers().OfType<IFieldSymbol>()
            .Any(f => SymbolEqualityComparer.Default.Equals(f.AssociatedSymbol, p));

    /// <summary>R3.4: the field types a struct may hold.</summary>
    /// <summary>R3.4; and a pair of such values (R26.10), which an enumerator's <c>Current</c> may be (R28).</summary>
    private static bool IsValueField(IrType type) => type is IrPrim or IrNamedType or IrTypeParamType ||
        type is IrUserSpecType { FStar: WellKnown.TupleType, Args: var args } && args.All(IsValueField);

    /// <summary>
    /// R3.9a: the field types a <c>[Spec]</c> struct may hold. Wider than R3.4 by exactly
    /// the spec-only types, and no wider: a ghost value still cannot own a resource, so an
    /// array or a class reference is refused here as it is there.
    /// </summary>
    private static bool IsSpecField(IrType type) => type switch
    {
        IrPrim or IrNamedType or IrSeqType => true,
        // R24.18. A `[SpecType]`/`[SpecBinding]` value is a pure F* value (an equality
        // comparer, say), and so is `T?` of one: neither owns a resource.
        IrUserSpecType => true,
        IrOptionType { Inner: IrUserSpecType } => true,
        _ => Sorted.IsComparer(type),
    };

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
                    Usings: s.Usings)
                {
                    TypeParameters = [.. WellKnown.AllTypeParameters(s.Symbol).Select(t => t.Name)],
                });
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
                Locations.From(f.Symbol.Locations.FirstOrDefault() ?? Location.None), f.Name, f.Mapped)
                {
                    IsOwned = f.Symbol is IFieldSymbol fs &&
                        Borrowing.OwnedFields(s.Symbol, known).Contains(fs, SymbolEqualityComparer.Default),
                })
            .ToImmutableArray();

        var refinements = ImmutableArray.CreateBuilder<IrExpr>();
        for (var i = 0; i < Refinements(s).Count(); i++)
            if (bound.TryGetValue($"{s.Symbol.Name}_refine_{i}", out var spec))
                refinements.Add(new ExprLowerer(spec.Model, known, diagnostics, specPosition: true)
                    .Lower(spec.Expression));

        return new IrStruct(
            Locations.From(s.Syntax.Identifier), WellKnown.StructName(s.Symbol), fields, refinements.ToImmutable())
        {
            IsSpecOnly = s.IsSpecOnly,
            TypeParameters = [.. WellKnown.AllTypeParameters(s.Symbol).Select(t => t.Name)],
        };
    }

    private static ImmutableArray<string> BuildTypeUsings(
        TypeDeclarationSyntax syntax, INamedTypeSymbol symbol)
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

        /// <summary>R27.3. <c>[Region]</c>: a plain representation owned as one region.</summary>
        public bool IsRegion { get; init; }
        public bool IsCyclic { get; init; }

        /// <summary>R9.6. The <c>override</c> of the base's <c>[Model]</c> — the forgetting function.</summary>
        public ExpressionSyntax? ForgetBody { get; init; }

        /// <summary>R9.21. Concrete and not `sealed`: split by <see cref="OpenClasses"/>.</summary>
        public bool IsOpen { get; init; }

    }

    /// <summary>
    /// Collects every annotated <c>sealed class</c>. A class is annotated when it carries
    /// a <c>[Model]</c> member, which R3.9 makes mandatory: without one there is nothing
    /// for the invariant to relate the representation to, and every method specification
    /// would collapse to memory safety.
    /// </summary>
    /// <summary>
    /// R25.12. A <c>partial</c> class is one class however many declarations it has: it is
    /// collected at the declaration that holds its <c>[Model]</c> member, or at its first.
    /// </summary>
    private static bool IsPrincipalDeclaration(
        ClassDeclarationSyntax syntax, INamedTypeSymbol symbol, WellKnown known)
    {
        var parts = symbol.DeclaringSyntaxReferences;
        if (parts.Length < 2) return true;
        var modelSyntax = symbol.GetMembers()
            .Where(m => Declarations.Has(m, known.ModelAttribute))
            .SelectMany(m => m.DeclaringSyntaxReferences)
            .FirstOrDefault();
        var principal = modelSyntax is null
            ? parts[0]
            : parts.FirstOrDefault(p => p.SyntaxTree == modelSyntax.SyntaxTree &&
                                        p.Span.Contains(modelSyntax.Span)) ?? parts[0];
        return principal.SyntaxTree == syntax.SyntaxTree && principal.Span == syntax.Span;
    }

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
                if (!IsPrincipalDeclaration(syntax, symbol, known)) continue;
                // R27.1. Under `[TranslateAnnotatedOnly]` a subclass nothing translates is
                // not part of the verified program at all, so its generic base is not a
                // hierarchy the translator has to encode: the base is verified at its exact
                // type (see `ExactType`).
                if (UntranslatedSubclass(symbol, known)) continue;
                // R27.57. A representation-sharing subclass is its base's class.
                if (Subclasses.IsAlias(symbol, known)) continue;
                // R32.13. A view is the record of its state, collected with the structs.
                if (Borrowing.IsView(symbol, known)) continue;
                if (RefuseGenericType(symbol, diagnostics)) continue;

                // R18.1. Every class the collector *looks at* is one it has spoken about:
                // if it rejects the class, the rejection is the diagnostic, and the
                // members must not then draw PALCS0530 as well. Recording the attempt is
                // what keeps one cause from producing a second, contradictory report.
                if (known.IsPlainLike(symbol) ||
                    symbol.GetMembers().Any(m => Declarations.Has(m, known.ModelAttribute)))
                    attempted.Add(symbol);

                var modelMembers = symbol.GetMembers()
                    .Where(m => Declarations.Has(m, known.ModelAttribute))
                    .ToImmutableArray();

                // R9.21b. A subclass of an open class inherits its base's representation,
                // and with it the abstraction function over that representation. C# gives
                // it no way to write one of its own: the base's `[Model]` member is a
                // concrete property over fields the subclass did not declare, and an
                // `override` of it would have nothing else to be written in terms of. So
                // the base's is the model it has, and R9.6's forgetting is the identity.
                if (modelMembers.Length == 0 && InheritedModel(symbol, known) is { } up)
                {
                    modelMembers = [up];
                    attempted.Add(symbol);
                }

                // R27.3. A `[Region]` class is a `[Plain]` representation whose objects an
                // owner holds as one region. Its optional `[Model]` is the view of one node.
                if (Declarations.Has(symbol, known.RegionAttribute))
                {
                    if (!symbol.IsSealed || symbol.BaseType?.SpecialType != SpecialType.System_Object)
                    {
                        diagnostics.Error("PALCS0700", Locations.From(syntax.Identifier),
                            $"`{symbol.Name}` is `[Region]` but is not a `sealed` class deriving from " +
                            "`object`. A region holds one record type, so the class cannot take part in " +
                            "a hierarchy (doc/translation.md R27.3).");
                        continue;
                    }
                    if (CollectPlainFields(symbol, known, diagnostics) is not { } regionFields)
                        continue;
                    var cyclic = Declarations.Find(symbol, known.RegionAttribute) is { } regionData &&
                                 Declarations.NamedFlag(regionData, "Cyclic");
                    var children = regionFields.Count(f =>
                        f.Mapped is IrClassType { Nullable: true } ct && ct.Name == symbol.Name);
                    if (children != 2)
                    {
                        diagnostics.Error("PALCS0701", Locations.From(syntax.Identifier),
                            $"`{symbol.Name}` is `[Region]` and declares {children} nullable field(s) of its " +
                            "own type. A region's shape is a binary tree: exactly two such fields, the " +
                            "left and right children in declaration order (doc/translation.md R27.3).");
                        continue;
                    }
                    ExpressionSyntax? viewBody = null;
                    IrType viewType = IrPrim.SpecIntType;
                    if (modelMembers.Length > 0)
                    {
                        if (modelMembers is not [IPropertySymbol vp] ||
                            vp.DeclaringSyntaxReferences.FirstOrDefault()?.GetSyntax()
                                is not PropertyDeclarationSyntax { ExpressionBody.Expression: { } vb } ||
                            known.MapType(vp.Type) is not { } vt)
                        {
                            diagnostics.Error("PALCS0702", Locations.From(syntax.Identifier),
                                $"The `[Model]` of the `[Region]` class `{symbol.Name}` must be one " +
                                "expression-bodied property of a translatable type: the view of one node " +
                                "(doc/translation.md R27.3).");
                            continue;
                        }
                        viewBody = vb;
                        viewType = vt;
                    }
                    result.Add(new ClassCandidate(
                        syntax, symbol, regionFields, modelMembers.FirstOrDefault() ?? symbol, viewType, viewBody,
                        [], BuildClassUsings(syntax, symbol))
                    {
                        IsPlain = true,
                        IsRegion = true,
                        IsCyclic = cyclic,
                    });
                    continue;
                }

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

                    // R20.1a. Under `[TranslateAnnotatedOnly]` such a method is translated
                    // receiver-free instead.
                    // R29.3. A borrowing class has its owner's model.
                    if (annotated && !known.AnnotatedOnly && !Borrowing.IsBorrowingClass(symbol, known))
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
                // or `abstract`, with a vtable and none. R9.21 admits the third case by
                // desugaring rather than by encoding it: a concrete class that is not
                // `sealed` is both at once, so it is split into one of each.

                if (!TryCollectClass(syntax, symbol, modelMembers[0], known, diagnostics, out var candidate))
                    continue;
                result.Add(candidate);
            }
        }
        return result.ToImmutable();
    }

    /// <summary>
    /// R27.1. A class nothing translates, deriving from a <em>generic</em> class. It has no
    /// annotation and none of its members has one. (A subclass of a non-generic class with a
    /// model inherits that model and is translated by R9.21b; a generic hierarchy has no
    /// translation at all, R15.1, which is what leaves this case free.)
    /// </summary>
    private static bool UntranslatedSubclass(INamedTypeSymbol symbol, WellKnown known) =>
        known.AnnotatedOnly &&
        symbol.BaseType is { SpecialType: not SpecialType.System_Object, TypeParameters.Length: > 0 } &&
        !Declarations.IsAnnotated(symbol, known) &&
        !symbol.GetMembers().Any(m => Declarations.IsAnnotated(m, known) ||
            m is IMethodSymbol { AssociatedSymbol: { } a } && Declarations.IsAnnotated(a, known));

    /// <summary>
    /// R27.1. Verification at the <em>exact type</em>. Under <c>[TranslateAnnotatedOnly]</c>,
    /// a concrete class that is not <c>sealed</c>, but whose every subclass in the
    /// compilation is untranslated (<see cref="UntranslatedSubclass"/>), is translated as a
    /// leaf even when it declares virtual members and even though it has subclasses. Its
    /// invariant is produced only by its own translated constructor, which runs only for a
    /// translated <c>new C(...)</c>: a subclass's constructor chains to the CLR's, never to
    /// the translation. So every receiver verified code holds has dynamic type exactly
    /// <c>C</c>, and every virtual call on it binds to <c>C</c>'s own body.
    /// </summary>
    private static bool ExactType(INamedTypeSymbol symbol, WellKnown known) =>
        !symbol.IsAbstract && !symbol.IsSealed &&
        symbol.TypeParameters.Length > 0 &&
        known.Compilation.GetSymbolsWithName(_ => true, SymbolFilter.Type)
            .OfType<INamedTypeSymbol>()
            .Where(t => SymbolEqualityComparer.Default.Equals(t.BaseType?.OriginalDefinition, symbol.OriginalDefinition))
            .ToList() is { Count: > 0 } subs &&
        // R27.57. A subclass sharing the representation is verified at its own exact type.
        subs.All(t => UntranslatedSubclass(t, known) || Subclasses.IsAlias(t, known) ||
                      // R32.13. A view's objects are records, never objects of the base.
                      Borrowing.IsView(t, known));

    /// <summary>
    /// R22.5. Under <c>[TranslateAnnotatedOnly]</c>, a class that is not <c>sealed</c> but
    /// declares no virtual or abstract member, and that no class in the compilation derives
    /// from, is a leaf: a subclass elsewhere can add state but cannot change what any of
    /// this class's methods do, so there is no vtable for R9.21 to split off.
    /// </summary>
    /// <summary>
    /// R27.46. The class an <c>[Exactly]</c> parameter is an object of, when it is one whose
    /// translated objects all have it as their dynamic type (R27.1) and which converts to the
    /// parameter's type by an implicit reference conversion.
    /// </summary>
    internal static INamedTypeSymbol? ExactParameter(IParameterSymbol p, Compilation compilation, WellKnown known) =>
        known.ExactClass(p) is { TypeKind: TypeKind.Class, IsAbstract: false } c && known.HasModel(c) &&
        (c.IsSealed || EffectivelySealed(c.OriginalDefinition, known)) &&
        compilation.ClassifyCommonConversion(c, p.Type) is { IsImplicit: true, IsReference: true }
            ? c : null;

    /// <summary>
    /// R32.13. The view a method's <c>[return: Exactly(typeof(C&lt;&gt;.V))]</c> names, as a
    /// member of the method's containing class (so at its type arguments).
    /// </summary>
    /// <summary>
    /// R32.13. A method returning a view of its receiver says so: a call holds the view it
    /// returns as borrowing the call's receiver, and this is what makes that sound.
    /// </summary>
    private static IEnumerable<IrExpr> ViewOwnerEnsures(IMethodSymbol method, IrType returnType, WellKnown known, IrLoc loc)
    {
        if (method.IsStatic || ExactReturn(method, known) is not { } view ||
            Borrowing.OwnerField(view, known) is not { } owner ||
            known.MapType(owner.Type) is not { } ownerType)
            yield break;
        yield return new IrBinary(loc, BinOp.Eq,
            new IrField(loc, new IrResult(loc) { Type = returnType }, owner.Name) { Type = ownerType },
            new IrRefOf(loc, Names.This) { Type = ownerType }) { Type = IrPrim.Bool };
    }

    internal static INamedTypeSymbol? ExactReturn(IMethodSymbol method, WellKnown known)
    {
        var attr = method.OriginalDefinition.GetReturnTypeAttributes()
            .FirstOrDefault(a => a.AttributeClass?.Name == "ExactlyAttribute");
        if (attr is not { ConstructorArguments: [{ Value: INamedTypeSymbol named }] }) return null;
        foreach (var t in method.ContainingType.GetTypeMembers(named.Name))
            if (Borrowing.IsView(t, known)) return t;
        return null;
    }

    internal static bool EffectivelySealed(INamedTypeSymbol symbol, WellKnown known) =>
        EffectivelySealedIn(Canonical(symbol, known), known);

    /// <summary>
    /// The symbol for <paramref name="symbol"/> in <c>known</c>'s compilation. A body is
    /// bound in a compilation of its own, whose symbols are not equal to the original's.
    /// </summary>
    private static INamedTypeSymbol Canonical(INamedTypeSymbol symbol, WellKnown known)
    {
        if (SymbolEqualityComparer.Default.Equals(symbol.ContainingAssembly, known.Compilation.Assembly)) return symbol;
        var name = symbol.MetadataName;
        for (var outer = symbol.ContainingType; outer is not null; outer = outer.ContainingType)
            name = outer.MetadataName + "+" + name;
        if (symbol.ContainingNamespace is { IsGlobalNamespace: false } ns) name = ns.ToDisplayString() + "." + name;
        return known.Compilation.GetTypeByMetadataName(name) ?? symbol;
    }

    private static bool EffectivelySealedIn(INamedTypeSymbol symbol, WellKnown known) =>
        ExactType(symbol, known) ||
        known.AnnotatedOnly &&
        // R24.4. An unannotated virtual has no module, so no translated body can call it
        // (R22.4's refusal at the call); a subclass overriding it changes nothing verified.
        !symbol.GetMembers().Any(m => (m.IsVirtual || m.IsAbstract || m.IsOverride) &&
            (Declarations.IsAnnotated(m, known) ||
             m is IMethodSymbol { AssociatedSymbol: { } a } && Declarations.IsAnnotated(a, known))) &&
        !known.Compilation.GetSymbolsWithName(_ => true, SymbolFilter.Type)
            .OfType<INamedTypeSymbol>()
            .Any(t => SymbolEqualityComparer.Default.Equals(t.BaseType?.OriginalDefinition, symbol.OriginalDefinition));

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
            if (Borrowing.IsBorrowingClass(type, known)) continue;   // R29.3

            // R29.4. An `object` field is not a value the scheme holds: it is not translated.
            if (known.MapType(type) is not { } mapped || WellKnown.IsObj(mapped))
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
            // R22.3. Under `[TranslateAnnotatedOnly]` an unannotated member is outside the
            // scope, not a construct to refuse; a call to it is refused where it is made.
            if (known.AnnotatedOnly && member is not IFieldSymbol) continue;

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
                // R9.20: a read-only computed property is the method its getter is.
                IPropertySymbol p when IsComputed(p, known) => (null, null),
                IMethodSymbol { MethodKind: MethodKind.Constructor } => (null, null),
                IMethodSymbol { MethodKind: MethodKind.Ordinary, IsOverride: true } m
                    when IsObjectMember(m) =>
                    ("an `override` of a member of `object`. R9.6 reads an `override` as the " +
                     "forgetting function of a translated base, and `System.Object` has no model " +
                     "(doc/translation.md R18.2), so this override has no other reading",
                     $"{symbol.Name}.{member.Name}"),
                IMethodSymbol { MethodKind: MethodKind.Ordinary } => (null, null),

                // R27.40. A read-only indexer whose getter is an accessor is collected as the
                // method `get_Item` it is (R22.13), and a read through it is a call of it.
                IPropertySymbol { IsIndexer: true, SetMethod: null, GetMethod: { } g }
                    when g.DeclaringSyntaxReferences.Any(r => r.GetSyntax() is AccessorDeclarationSyntax) => (null, null),
                IPropertySymbol { IsIndexer: true } =>
                    ("an indexer. Indexing a translated object has no rule: `a[i]` is the array " +
                     "subscript of R6.5 and nothing else (doc/translation.md R18.2)",
                     $"{symbol.Name}.this[]"),
                IPropertySymbol { SetMethod: not null } =>
                    ("a property with a `set` accessor. R9.20 translates a computed property as the " +
                     "method its getter is, but a setter's parameter is named `value` by C# rather " +
                     "than by the author, and §4 has no reading of that name in a specification " +
                     "(doc/translation.md R9.20b). Write the assignment as an ordinary method",
                     $"{symbol.Name}.{member.Name}"),
                IPropertySymbol =>
                    ("a property whose accessor pal-csharp cannot read as a method " +
                     "(doc/translation.md R9.20)", $"{symbol.Name}.{member.Name}"),
                // R22.7. A `const` is folded where it is read (R20.10's reading of a value
                // the field always denotes), so it needs nothing of its own.
                IFieldSymbol { IsConst: true } when known.AnnotatedOnly => (null, null),
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
        // R9.21b. The `[Model]` member is the base's, not this class's: the representation
        // it abstracts is one this class inherits rather than declares.
        var inheritedModel =
            !SymbolEqualityComparer.Default.Equals(modelSymbol.ContainingType, symbol);
        var ok = true;

        var fields = ImmutableArray.CreateBuilder<StructField>();
        var observations = ImmutableArray.CreateBuilder<ObservationMember>();

        // R9.21b. A subclass of an open class inherits its representation. The inherited
        // fields are collected *here*, ahead of the class's own, rather than merged into
        // the IR later: the abstraction function inherited with them is the base's
        // expression, and it has to be lowered somewhere those names resolve.
        foreach (var member in Inherited(symbol))
        {
            // R4.13: global mutable state is covered by no per-object invariant.
            // R22.8: a `static readonly` field is not mutable state; R20.10 reads it as its
            // initializer.
            if (member is IFieldSymbol { IsStatic: true, IsConst: false, IsReadOnly: false } stat)
            {
                diagnostics.Error("PALCS0522",
                    Locations.From(stat.Locations.FirstOrDefault() ?? Location.None),
                    $"`{symbol.Name}.{stat.Name}` is a static mutable field. No per-object invariant " +
                    "covers it, so nothing in the scheme can say what it holds.");
                ok = false;
                continue;
            }

            // R24.17: a `[PulseBody]` spec function has no C# body to observe through.
            if (Declarations.Has(member, known.SpecAttribute) &&
                !Declarations.Has(member, known.PulseBodyAttribute) &&
                Body(member) is { } observationBody &&
                ReturnTypeOf(member) is { } observationType)
            {
                // R9.21d. An observation is written against the model member of the class
                // that declares it, so it may be inherited exactly while the model is that
                // same member -- R9.21b's inherited-whole case, where the forgetting is the
                // identity. Once a class between here and there supplies a model of its
                // own, the earlier observation belongs to the earlier model and is reached
                // through R9.6's forgetting, as it is from an abstract base; copying its
                // body down would read a model member that is no longer the model.
                //
                // The comparison is against the *model's* declaring class and not this one,
                // because a class may inherit its model from a base that itself extended
                // one: `Pallet : Crate : Box` inherits `Crate`'s model whole and must take
                // `Crate`'s observations with it, but not `Box`'s.
                if (!SymbolEqualityComparer.Default.Equals(
                        member.ContainingType, modelSymbol.ContainingType))
                    continue;

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

            // R29.3. A cached view object that borrows this class (`keyList ??= new KeyList(this)`)
            // is not part of its representation either.
            // A read or write of it is refused as for R25.3, except the fill of R29.3b.
            if (Borrowing.IsBorrowingClass(type, known)) continue;
            var mapped = known.MapType(type);
            // R29.4. An `object` field (a `_syncRoot`) is not part of the representation:
            // `obj` is a translation of values in flight, not of state.
            if (WellKnown.IsObj(mapped)) mapped = null;
            // R25.3. Under `[TranslateAnnotatedOnly]` a field whose type has no translation
            // -- a cache of an unannotated view object, say -- is left out of the
            // representation, as an unannotated method is left out of the class. A read or
            // write of it from translated code finds no field and is refused.
            if (mapped is null && known.AnnotatedOnly) continue;
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
            // R24.2. A field of a `[SpecType]` or bound library type (R20.11, R21.5) -- a
            // comparer -- is a value too: the type is opaque, so the record holds it and
            // nothing else can. R25.1. A comparer is a value like a type parameter's.
            if (mapped is not (IrPrim or IrNamedType or IrArrayType or IrClassType or IrTypeParamType
                    or IrUserSpecType or IrOptionType { Inner: IrUserSpecType }) &&
                !Sorted.IsComparer(mapped))
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
        // R22.4. Under `[TranslateAnnotatedOnly]` the clause is not refused: no call through
        // an interface translates (its members have no module), so the class is verified
        // as itself, and an interface-typed call is refused at the call.
        foreach (var iface in known.AnnotatedOnly ? [] : symbol.Interfaces)
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
            // R9.21. A `sealed` base really is a vtable value and nothing else, so there
            // is no type to derive from. An *open* one is both, and the split gives it an
            // abstract half — which is the vtable type this derivation names.
            else if (!b.IsAbstract && b.IsSealed)
            {
                diagnostics.Error("PALCS0540", Locations.From(syntax.Identifier),
                    $"`{symbol.Name}` derives from `{b.Name}`, which is `sealed`. A base class " +
                    "supplies a vtable *type*, and a sealed class supplies only a vtable *value*; " +
                    "doc/translation.md R9.4 keeps those apart. Drop the `sealed`.");
                ok = false;
            }
            else baseSymbol = b;
        }

        // R9.3. Every virtual method is abstract. A `virtual` method with a body would be
        // inherited by a subclass that does not override it, and a base method body can
        // only run against a representation the base does not have. The abstract ones are
        // not collected here: they are ordinary method candidates with no body, so their
        // contracts are bound by the machinery every other method's contract uses.
        //
        // R9.21 admits the body on an *open* class, where it is not a claim about an
        // abstract class at all: the split puts the body on a leaf that does have a
        // representation, and gives every other leaf a copy.
        foreach (var m in symbol.GetMembers().OfType<IMethodSymbol>()
                     .Where(m => m.MethodKind == MethodKind.Ordinary))
        {
            if (m.IsVirtual && !m.IsAbstract && symbol.IsAbstract)
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
        //
        // R9.21b. Not when the base is open and the model was inherited from it: the two
        // models are then the *same* model, so the forgetting function is the identity and
        // there is nothing for the subclass to say. Demanding an override here would be
        // demanding one C# does not allow, since the member being inherited is concrete.
        ExpressionSyntax? forgetBody = null;
        if (baseSymbol is not null && !inheritedModel)
        {
            var forget = symbol.GetMembers()
                .FirstOrDefault(m => m.IsOverride && OverriddenChainHasModel(m, known));

            // R9.5 and R9.6 are two functions, and they read different things: the
            // abstraction function is written over the *fields*, the forgetting function
            // over this class's own *model*. One member cannot be both, and a member
            // marked `[Model]` that is also the override of the base's is asking it to be.
            // Left alone this surfaces as PALCS0001 on a field name -- the forgetting
            // lowering sees the abstraction's body and reports the field as unknown, which
            // is true of that lowering and useless to the reader.
            if (forget is not null && SymbolEqualityComparer.Default.Equals(forget, modelSymbol))
            {
                diagnostics.Error("PALCS0543",
                    Locations.From(forget.Locations.FirstOrDefault() ?? Location.None),
                    $"`{symbol.Name}.{forget.Name}` is marked `[Model]` and also overrides " +
                    $"`{baseSymbol.Name}`'s `[Model]` member, so it is being asked to be both this " +
                    "class's abstraction function and its forgetting function. Those read different " +
                    "things -- the abstraction function reads the fields, the forgetting function " +
                    "reads this class's model (doc/translation.md R9.5, R9.6) -- so they are two " +
                    $"members: keep `[Model]` on a new member of `{symbol.Name}`'s own, and leave the " +
                    "override to say what the base's model is in terms of it.");
                return false;
            }

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
            IsOpen = !symbol.IsAbstract && !symbol.IsSealed && !EffectivelySealed(symbol, known),
            ForgetBody = forgetBody,
        };
        return true;
    }

    /// <summary>The semantic model for a node's own tree, which may not be the class's.</summary>
    private static SemanticModel In(SemanticModel model, SyntaxNode node) =>
        node.SyntaxTree == model.SyntaxTree ? model : model.Compilation.GetSemanticModel(node.SyntaxTree);

    /// <summary>
    /// R9.21b. The class's own members, preceded by the representation it inherits from
    /// every open base, base-most first. Only the representation is inherited: an
    /// observation is a statement about the model and the model is inherited whole, so
    /// restating it on the subclass would emit a second name for one function.
    /// </summary>
    private static IEnumerable<ISymbol> Inherited(INamedTypeSymbol symbol)
    {
        var chain = new List<INamedTypeSymbol>();
        for (var b = symbol.BaseType; b is { IsAbstract: false, IsSealed: false }; b = b.BaseType)
            chain.Insert(0, b);
        foreach (var b in chain)
            foreach (var m in b.GetMembers())
                if (m is IFieldSymbol { IsStatic: false, IsConst: false, AssociatedSymbol: null } or
                         IPropertySymbol { IsStatic: false, IsIndexer: false })
                    yield return m;
        foreach (var m in symbol.GetMembers()) yield return m;
    }

    /// <summary>
    /// R9.21b. The <c>[Model]</c> member a class inherits from the nearest open base that
    /// declares one. Only an <em>open</em> base: a sealed class cannot be derived from, and
    /// an abstract one declares its model abstract, which R9.6 already makes every subclass
    /// supply for itself.
    /// </summary>
    private static ISymbol? InheritedModel(INamedTypeSymbol symbol, WellKnown known)
    {
        for (var b = symbol.BaseType; b is not null; b = b.BaseType)
        {
            if (b.IsAbstract || b.IsSealed) return null;
            if (b.GetMembers().FirstOrDefault(m => Declarations.Has(m, known.ModelAttribute))
                is { } model) return model;
        }
        return null;
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
            // R31.3. An invariant may name the object itself, as `@this`.
            var fieldParams = c.Fields.Select(f => new SpecParam(f.Name, f.Type))
                .Append(new SpecParam(Names.This, c.Symbol)).ToImmutableArray();
            var index = 0;
            foreach (var (text, location) in ClassInvariants(c))
                sites.Add(new SpecSite(
                    Key: $"{c.Symbol.Name}_invariant_{index++}",
                    Text: text,
                    Location: location,
                    Parameters: fieldParams,
                    Usings: c.Usings)
                {
                    TypeParameters = [.. c.Symbol.TypeParameters.Select(t => t.Name)],
                });

            index = 0;
            foreach (var (text, location) in ModelRefinements(c))
                sites.Add(new SpecSite(
                    Key: $"{c.Symbol.Name}_model_refine_{index++}",
                    Text: text,
                    Location: location,
                    Parameters: ReturnTypeOf(c.ModelSymbol) is { } mt
                        ? [new SpecParam(SpecBinder.ResultParameter, mt)]
                        : ImmutableArray<SpecParam>.Empty,
                    Usings: c.Usings)
                {
                    TypeParameters = [.. c.Symbol.TypeParameters.Select(t => t.Name)],
                });
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
                case IrRaise ra: Walk(ra.Exception); return;
                case IrOld o2: Walk(o2.Operand); return;
                case IrLive lv: Walk(lv.Operand); return;
                case IrNewArray na: Walk(na.Length); if (na.Source is { } nas) Walk(nas); return;
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
                IsNullableArray = f.Symbol is IFieldSymbol
                {
                    Type: IArrayTypeSymbol, NullableAnnotation: NullableAnnotation.Annotated,
                },
            })
            .ToImmutableArray();

        // R12.1. Everything below this point derives something from the model — the
        // abstraction, the invariant, the observations, the recursion. A `[Plain]` class
        // has no model, so it stops here with just its fields.
        if (c.IsPlain)
            return new IrClass(
                Locations.From(c.Syntax.Identifier), c.Symbol.Name, fields,
                ModelMember: "", ModelType: c.ModelType,
                // R27.7. A region class's view reads its fields, as an abstraction does.
                ModelBody: c.ModelBody is null ? null
                    : new ExprLowerer(In(classModel, c.ModelBody), known, diagnostics, specPosition: true)
                      { ClassMembers = c.Fields.Select(f => f.Name).ToImmutableHashSet() }.Lower(c.ModelBody),
                ModelRefinements: [], Invariants: [], Observations: [])
            {
                IsPlain = true,
                IsRegion = c.IsRegion,
                IsCyclic = c.IsCyclic,
                TypeParameters = c.IsRegion
                    ? [.. WellKnown.OuterAndOwnTypeParameters(c.Symbol).Select(t => t.Name)]
                    : [.. c.Symbol.TypeParameters.Select(t => t.Name)],
            };

        // The abstraction reads the fields; an observation reads the model. Both are
        // written unqualified inside the class, which is the same convention R3.4 uses
        // for a struct's [Refine].
        var fieldNames = c.Fields.Select(f => f.Name).ToImmutableHashSet();
        var modelName = ImmutableHashSet.Create(c.ModelSymbol.Name);

        // R9.2. An abstract class has no abstraction function: there are no fields to
        // abstract from, and each leaf supplies the model instead.
        // R9.21b. An inherited abstraction function is a syntax node in the *base's* file,
        // and a semantic model does not span trees. It is the model body's own tree that
        // has to be asked about it, which for every class that declares its own is the
        // same tree as before.
        var modelBody = c.ModelBody is null
            ? null
            : new ExprLowerer(In(classModel, c.ModelBody), known, diagnostics, specPosition: true)
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
                new ExprLowerer(In(classModel, o.Body), known, diagnostics, specPosition: true)
                { ClassMembers = modelName }.Lower(o.Body)))
            .ToImmutableArray();

        return new IrClass(
            Locations.From(c.Syntax.Identifier), c.Symbol.Name, fields,
            c.ModelSymbol.Name, c.ModelType, modelBody, refinements.ToImmutable(),
            invariants.ToImmutable(), observations)
        {
            BaseClass = c.BaseSymbol?.Name,
            IsAbstract = c.IsAbstract,
            IsOpen = c.IsOpen,
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
        known.IsPlainLike(n);

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
            foreach (var (attribute, index, wantsResult) in SpecAttributes(candidate.Declaration, known))
            {
                var text = Declarations.StringArgument(attribute);
                if (text is null) continue;
                // R32.13. A clause for the replica at a view is over the view.
                var atView = AtView(attribute, candidate.Symbol, known);
                sites.Add(new SpecSite(
                    Key: $"{Naming.Of(candidate.Symbol)}_{index}",
                    Text: text,
                    Location: Declarations.ArgumentLocation(attribute),
                    Parameters: ShimParameters(candidate.Symbol, compilation, known, wantsResult, atView),
                    Usings: usings)
                {
                    TypeParameters = atView is null ? SiteTypeParameters(candidate.Symbol, known)
                        : [.. WellKnown.AllTypeParameters(atView).Select(t => t.Name), .. candidate.Symbol.TypeParameters.Select(t => t.Name)],
                    // R28.3. A contract about a borrowing struct names its private state.
                    Private = candidate.Symbol.DeclaredAccessibility == Accessibility.Private ||
                              atView is not null ||
                              Borrowing.IsMember(candidate.Symbol, known) ||
                              Borrowing.IsBorrowing(candidate.Symbol.ReturnType, known) ||
                              // R29.4. A boxed result is described by the state of what it boxes.
                              WellKnown.IsObjectLike(candidate.Symbol.ReturnType),
                });
            }

            // R19.2. A `[Throws]` predicate is over the parameters and `Thrown`, the
            // exception at its declared type. It describes an abortive exit, so there is
            // no `Result` to name.
            foreach (var (attribute, k, thrown) in ThrowsAttributes(candidate.Declaration, known))
            {
                sites.Add(new SpecSite(
                    Key: $"{Naming.Of(candidate.Symbol)}_throws_{k}",
                    Text: Declarations.StringArgument(attribute, 1) ?? "true",
                    Location: Declarations.ArgumentLocation(attribute, 1),
                    Parameters: [.. ShimParameters(candidate.Symbol, compilation, known, false),
                                 new SpecParam(ThrownParameter, thrown)],
                    Usings: usings)
                {
                    TypeParameters = SiteTypeParameters(candidate.Symbol, known),
                    Private = candidate.Symbol.DeclaredAccessibility == Accessibility.Private ||
                              Borrowing.IsMember(candidate.Symbol, known),
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
        var own = candidate.Symbol.ContainingType.IsGenericType ||
                  WellKnown.OuterAndOwnTypeParameters(candidate.Symbol.ContainingType).Any()
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

    /// <summary>R19.2. The name a <c>[Throws]</c> predicate gives the exception.</summary>
    public const string ThrownParameter = "Thrown";

    /// <summary>
    /// R19.2. The <c>[Throws(typeof(E), "…")]</c> attributes of a method, numbered in
    /// declaration order, with <c>E</c>. An argument that is not an exception type is
    /// reported where the clause is read (<see cref="ReadSpecs"/>) and skipped here.
    /// </summary>
    private static IEnumerable<(AttributeData Attribute, int Index, ITypeSymbol Thrown)> ThrowsAttributes(
        ISymbol symbol, WellKnown known)
    {
        var index = 0;
        foreach (var a in symbol.GetAttributes())
        {
            if (!Same(a.AttributeClass, known.ThrowsAttribute)) continue;
            var k = index++;
            if (a.ConstructorArguments is [{ Value: ITypeSymbol t }, ..] &&
                known.MapType(t) is IrExnType)
                yield return (a, k, t);
        }
    }

    /// <summary>The spec-bearing attributes of a method, in declaration order.</summary>
    /// <remarks>
    /// R9.20: the declaration, not the symbol. For a computed property these differ —
    /// the body is the accessor's and the attributes are the property's, because C# does
    /// not permit an attribute on an accessor. For everything else they are the same.
    /// </remarks>
    private static IEnumerable<(AttributeData Attribute, int Index, bool WantsResult)> SpecAttributes(
        ISymbol symbol, WellKnown known)
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
        // R27.16. A region class nested in a generic class is generic in the outer parameters (R27.3).
        .. (symbol.ContainingType is { } ct && WellKnown.IsRegionDeclaration(ct)
            ? WellKnown.OuterAndOwnTypeParameters(ct).Select(t => t.Name)
            : symbol.ContainingType?.TypeParameters.Select(t => t.Name) ?? []),
        .. symbol.TypeParameters.Select(t => t.Name),
    ];

    /// <summary>R28.2. A borrowing struct's member is generic in its enclosing types' parameters.</summary>
    private static ImmutableArray<string> SiteTypeParameters(IMethodSymbol symbol, WellKnown known) =>
        Borrowing.IsMember(symbol, known)
            ? [.. WellKnown.AllTypeParameters(symbol.ContainingType).Select(t => t.Name),
               .. symbol.TypeParameters.Select(t => t.Name)]
            : MethodTypeParameters(symbol);

    private static bool Same(ISymbol? a, ISymbol b) => SymbolEqualityComparer.Default.Equals(a, b);

    /// <summary>
    /// The binders a specification is entitled to see: the method's parameters by value
    /// (a spec talks about values, not storage), ghost parameters unwrapped from
    /// <c>Ghost&lt;T&gt;</c>, and — in a postcondition — <c>Result</c>.
    /// </summary>
    /// <summary>
    /// R32.13. The view a contract attribute's <c>At</c> names, as a member of the class
    /// <paramref name="symbol"/> is declared in; <c>null</c> when it names none.
    /// </summary>
    internal static INamedTypeSymbol? AtView(AttributeData attribute, IMethodSymbol symbol, WellKnown known)
    {
        if (attribute.NamedArguments.FirstOrDefault(a => a.Key == "At").Value.Value is not INamedTypeSymbol at)
            return null;
        var holder = symbol.ContainingType;
        var view = holder?.GetTypeMembers(at.Name).FirstOrDefault(t =>
            SymbolEqualityComparer.Default.Equals(t.OriginalDefinition, at.OriginalDefinition));
        return view is not null && Borrowing.IsView(view, known) ? view : null;
    }

    private static ImmutableArray<SpecParam> ShimParameters(
        IMethodSymbol symbol, Compilation compilation, WellKnown known, bool wantsResult,
        INamedTypeSymbol? atView = null)
    {
        var result = ImmutableArray.CreateBuilder<SpecParam>();

        // R4.10a. A spec string is compiled as the body of a *static* shim method, where
        // a bare `this` is C# error CS0026, so the receiver has to be an ordinary
        // parameter. Naming it `this` makes it render as the verbatim identifier `@this`
        // (SpecBinder.RenderParam), which is legal C#, binds correctly, and needs no
        // machinery of its own. A constructor has no receiver in its contract: the object
        // does not exist until it returns, and R4.12 constrains the *initial model*
        // through `Result` instead.
        if (symbol is { IsStatic: false,
                        MethodKind: MethodKind.Ordinary or MethodKind.Constructor
                                    or MethodKind.PropertyGet or MethodKind.PropertySet
                                    or MethodKind.ExplicitInterfaceImplementation } ||
            Borrowing.IsMember(symbol, known))
            result.Add(new SpecParam(Names.This, atView ?? symbol.ContainingType));

        foreach (var p in symbol.Parameters)
        {
            var type = known.IsGhost(p.Type) ? ((INamedTypeSymbol)p.Type).TypeArguments[0] : p.Type;
            // R27.46. An `[Exactly]` parameter is an object of its class in the contract too.
            if (ExactParameter(p, compilation, known) is { } exact) type = exact;
            result.Add(new SpecParam(p.Name, type));
        }
        // R20.12. A receiver-free method's contract may name the receiver's readonly fields
        // it takes, by their own names -- unless a parameter shadows one, as in C#.
        foreach (var f in ContextNames(symbol, compilation, known).Values)
            result.Add(new SpecParam(f.Name, Declarations.ContextType(f)));

        if (wantsResult && !symbol.ReturnsVoid)
            result.Add(new SpecParam(SpecBinder.ResultParameter, ExactReturn(symbol, known) ?? symbol.ReturnType));

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
        DiagnosticBag diagnostics, List<IrMethod>? lifted = null)
    {
        var symbol = candidate.Symbol;
        var loc = Locations.From(candidate.Identifier);

        // §28. A member of a borrowing struct is a member of the borrowed object's class.
        // R27.41. Its `[Spec]` properties are abbreviations, expanded where they are read.
        if (Borrowing.IsMember(symbol, known) && symbol.AssociatedSymbol is IPropertySymbol bsp &&
            Declarations.Has(bsp, known.SpecAttribute))
            return null;
        if (Borrowing.IsMember(symbol, known))
            return LowerBorrowingMember(candidate, model, known, bound, diagnostics, loc, lifted);
        // R32.13. A base member verified again at a view is a member of the view.
        if (known.Replica is { At: var replicaAt } && Borrowing.IsView(replicaAt, known))
            return LowerBorrowingMember(candidate, model, known, bound, diagnostics, loc, lifted, replicaAt);

        var specs = ReadSpecs(symbol, candidate.Declaration, known, bound, diagnostics);
        var parameters = LowerParameters(symbol, model, known, diagnostics);
        // R20.12. A receiver-free method takes the receiver's readonly fields it reads.
        if (Declarations.IsReceiverFree(symbol, known))
            parameters = [.. parameters, .. Declarations.ContextFields(symbol.ContainingType, model.Compilation, known)
                .Select(f => new IrParam(loc, Declarations.ContextName(f), known.MapType(Declarations.ContextType(f))!, ParamMode.Value) { IsContext = true })];
        if (symbol is { IsStatic: false,
                        MethodKind: MethodKind.Ordinary or MethodKind.PropertyGet or MethodKind.PropertySet
                                    or MethodKind.ExplicitInterfaceImplementation,
                        ContainingType: { } self } &&
            (known.HasModel(self) || known.IsRegionClass(self)))
        {
            // R15.3. The receiver of a method of `Node<T>` is a `Node<T>`, not a `Node`.
            // R27.16. A region object's receiver is a non-null reference into the region.
            var selfType = known.MapType(self) ?? new IrClassType(self.Name);
            if (known.IsRegionClass(self) && selfType is IrClassType st) selfType = st with { Nullable = false };
            parameters = [new IrParam(loc, Names.This, selfType, ParamMode.Value) { Plain = known.IsRegionClass(self) },
                          .. parameters];
        }

        if (candidate.Kind == CalleeKind.Spec)
            return LowerSpecFunction(candidate, model, known, diagnostics, loc, parameters, specs);

        // R27.42. An iterator method returns the sequence of the values it yields.
        var iterated = Iterators.Element(symbol) is { } yieldedType ? known.MapType(yieldedType) : null;
        if (Iterators.Element(symbol) is not null && !IteratorAdmissible(symbol, model, known, diagnostics, loc))
            return null;
        var returnType = symbol.MethodKind == MethodKind.Constructor
            ? known.MapType(symbol.ContainingType) ?? new IrClassType(symbol.ContainingType.Name)
            : iterated is not null ? new IrSeqType(iterated)
            // R30.29. A lookup returning a reference that may be null returns an `option`.
            : RefSnapshots.IsSnapshot(symbol, model.Compilation) && known.MapType(symbol.ReturnType) is { } snapshotOf
                ? new IrOptionType(snapshotOf)
            // R32.13. A method returning a view exactly returns its record.
            : known.MapType(ExactReturn(symbol, known) ?? symbol.ReturnType);
        if (returnType is null)
        {
            diagnostics.Unsupported(loc, $"The return type `{symbol.ReturnType}`");
            return null;
        }

        var declaringClass = symbol is { IsStatic: false, ContainingType: { } owner } && known.HasModel(owner)
            ? Subclasses.AliasBase(owner, known)?.Name ?? owner.Name
            : null;

        var objectFields = symbol.ContainingType is not { } holder ? ImmutableHashSet<string>.Empty
            // R27.16. A region object's fields, auto-properties included (R27.3), are its own.
            : known.IsRegionClass(holder) && !symbol.IsStatic
            ? holder.GetMembers().OfType<IFieldSymbol>()
                .Where(f => !f.IsStatic && !f.IsConst)
                .Select(f => f.AssociatedSymbol?.Name ?? f.Name)
                .ToImmutableHashSet()
            : !known.HasModel(holder)
            ? ImmutableHashSet<string>.Empty
            // R9.21b. A body inherits the representation of every open base, so a field
            // the class did not declare is still one of its own to read.
            : Inherited(holder).OfType<IFieldSymbol>()
                .Where(f => !f.IsStatic && !f.IsImplicitlyDeclared)
                .Select(f => f.Name)
                .ToImmutableHashSet();

        var lowerer = new StmtLowerer(model, known, diagnostics, objectFields);
        lowerer.Expressions.LiftPrefix = known.Replica?.Name ?? Naming.Of(symbol);
        lowerer.Expressions.LiftTypeParameters = MethodTypeParameters(symbol);
        if (iterated is not null) lowerer.Iterate(iterated);

        // R20.2. An `[Admit]`ted body is not translated: its contract is assumed, so the
        // body is never looked at, and refusing a construct in it would be refusing
        // something the translation does not depend on. That is what lets a trusted method
        // call code that is not translated at all -- the reason to admit it.
        var admitted = Declarations.Has(symbol, known.AdmitAttribute);
        // R24.17. A `[Spec]` (or `[Lemma]`) function's `[PulseBody]` replaces its C# body,
        // which is then never looked at: it has `=> throw …` or `{ }` for C# to compile.
        // On any other method both are kept, and the pair is refused (PALCS0503).
        var verbatim = Declarations.Has(symbol, known.PulseBodyAttribute) &&
                       (Declarations.Has(symbol, known.SpecAttribute) || Declarations.Has(symbol, known.LemmaAttribute));
        var body = admitted || verbatim ? null : LowerBody(candidate.Syntax, lowerer);

        // Body-level contracts (surface option A2) lead the body and are equivalent to
        // the attribute form; both produce the same IR.
        var (bodyRequires, bodyEnsures, trimmed) =
            ExtractBodyContracts(candidate.Syntax, model, known, lowerer, lowerRest: !admitted);

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

        lifted?.AddRange(lowerer.Expressions.Lifted);
        return new IrMethod(
            loc, Naming.Of(symbol), parameters, returnType,
            [.. specs.Requires, .. bodyRequires],
            [.. specs.Ensures, .. bodyEnsures, .. ViewOwnerEnsures(symbol, returnType, known, loc)],
            specs.Decreases,
            admitted || verbatim ? null
            : iterated is not null && (trimmed ?? body) is { } iteratorBody ? lowerer.WrapIterator(iteratorBody)
            : trimmed ?? body)
        {
            IsIterator = iterated is not null,
            IsLemma = candidate.Kind == CalleeKind.Lemma,
            PulseBody = pulseBody,
            Admit = admitted,
            RlimitFactor = Declarations.Find(symbol, known.RlimitAttribute) is { ConstructorArguments: [{ Value: int factor }] } && factor > 0
                ? factor : null,
            Open = Declarations.Has(symbol, known.OpenAttribute),
            Preserves = specs.Preserves,
            Throws = specs.Throws,
            AtThrows = specs.AtThrows,
            DeclaringClass = declaringClass,
            IsConstructor = symbol.MethodKind == MethodKind.Constructor,
            // R4.11b derives this from the write set. R9.7: an abstract method has no
            // write set, so [Frac] on the method says it instead — the same statement
            // R4.9a makes about a parameter, made about the receiver. R4.11c is why the
            // two can only *agree*: where there is a body, the write set is the truth and
            // a `[Frac]` that contradicts it has already been refused.
            IsReadOnly = declaringClass is not null &&
                symbol.MethodKind != MethodKind.Constructor &&
                (Declarations.Has(symbol, known.FracAttribute) ||
                 (!symbol.IsAbstract && !Declarations.Mutates(candidate.Syntax, model, known))),
            IsAbstract = symbol.IsAbstract,
            // R14.2. Type parameters become binders ahead of every value parameter. The
            // constrained case never reaches here: MapType declines a constrained type
            // parameter, so the signature that mentions it is refused first.
            TypeParameters = MethodTypeParameters(symbol),
            DefaultedTypeParameters = [.. MethodTypeParameters(symbol).Where(lowerer.Defaulted)],
            Overrides = symbol is { IsOverride: true, ContainingType.BaseType.Name: { } baseName } &&
                        !Subclasses.IsAlias(symbol.ContainingType, known)
                ? baseName
                : null,
        };
    }

    /// <summary>
    /// R27.42. An iterator method is verified as one whole enumeration, which is what a
    /// client observes when nothing else runs while it enumerates — the iterator's state is
    /// then its own. So the enumeration must not write what the client could see: the
    /// receiver is read-only, and every parameter is a value.
    /// </summary>
    private static bool IteratorAdmissible(IMethodSymbol symbol, SemanticModel model, WellKnown known,
        DiagnosticBag diagnostics, IrLoc loc)
    {
        var syntax = symbol.DeclaringSyntaxReferences.FirstOrDefault()?.GetSyntax();
        var reason =
            symbol.Parameters.FirstOrDefault(p => p.Type.IsReferenceType || p.Type.TypeKind == TypeKind.TypeParameter && !p.Type.IsValueType) is { } rp
                ? $"its parameter `{rp.Name}` is a reference, which the enumeration could share with its client"
            : syntax is null || (!symbol.IsStatic && Declarations.Mutates(syntax, model, known))
                ? "it writes its receiver"
            : null;
        if (reason is null) return true;
        diagnostics.Error("PALCS0712", loc,
            $"The iterator method `{symbol.Name}`: {reason}. An iterator is verified as one whole " +
            "enumeration, which is what its client observes only when the enumeration writes nothing " +
            "the client can see (doc/translation.md R27.42).");
        return false;
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
            ?? BlockOf(candidate.Syntax)?.Statements
                .OfType<ReturnStatementSyntax>().FirstOrDefault()?.Expression;

        // R24.17. A `[Spec]` function may be defined in F*: `[PulseBody]` is its body, and
        // the C# body (`=> throw …`) is not looked at.
        if (Declarations.Find(candidate.Symbol, known.PulseBodyAttribute) is { } verbatim)
            return new IrSpecFunction(loc, Naming.Of(candidate.Symbol), parameters, returnType,
                specs.Requires, new IrLiteral(loc, true) { Type = IrPrim.Bool })
            {
                TypeParameters = MethodTypeParameters(candidate.Symbol),
                PulseBody = Declarations.StringArgument(verbatim),
            };

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

    /// <summary>
    /// The statement block a declaration's body is written in, if it has one. R9.20 makes
    /// this a question with three answers rather than two: a method's, a constructor's,
    /// and — for a computed property — its getter's.
    /// </summary>
    private static BlockSyntax? BlockOf(SyntaxNode syntax) => syntax switch
    {
        BaseMethodDeclarationSyntax m => m.Body,
        PropertyDeclarationSyntax p => Candidate.Getter(p)?.Body,
        AccessorDeclarationSyntax a => a.Body,
        _ => null,
    };

    private static ArrowExpressionClauseSyntax? ArrowOf(SyntaxNode syntax) => syntax switch
    {
        BaseMethodDeclarationSyntax m => m.ExpressionBody,
        PropertyDeclarationSyntax p => p.ExpressionBody ?? Candidate.Getter(p)?.ExpressionBody,
        IndexerDeclarationSyntax ix => ix.ExpressionBody,
        AccessorDeclarationSyntax a => a.ExpressionBody,
        _ => null,
    };

    private static IrStmt? LowerBody(SyntaxNode syntax, StmtLowerer lowerer)
    {
        // R4.12c. A constructor initializer is not part of the body in Roslyn's tree, and
        // reading only the body is how `: this(…)` used to vanish -- leaving a constructor
        // that appeared to assign nothing and was reported for leaving its fields unset,
        // which is R18.1's failure exactly: the diagnostic named a symptom of a construct
        // nobody had looked at. It is lowered here, ahead of the body, because that is
        // where C# runs it.
        if (syntax is ConstructorDeclarationSyntax c)
        {
            var stmts = ImmutableArray.CreateBuilder<IrStmt>();
            if (c.Initializer is { } chained)
                stmts.Add(new IrExprStmt(Locations.From(chained),
                    lowerer.Expressions.LowerConstructorInitializer(chained)));
            else if (lowerer.Expressions.ImplicitBaseConstructor(c) is { } implicitBase)
                // R27.57. A representation-sharing subclass's constructor without an
                // initializer runs `: base()`, which builds the object.
                stmts.Add(new IrExprStmt(Locations.From(c), implicitBase));
            else
                // R4.12d. A field initialiser is the assignment C# would run here, and it
                // runs in *this* constructor precisely when this constructor does not chain
                // to another of its own class -- which is C#'s own rule, not a choice.
                stmts.AddRange(FieldInitialisers(c, lowerer));

            // R33.13. `C(T v) => _f = v;` is the body `{ _f = v; }`.
            var rest = c.Body is { } body ? lowerer.Lower(body)
                : c.ExpressionBody is { } ctorArrow ? lowerer.LowerArrow(ctorArrow) : null;
            if (rest is IrBlock inner) stmts.AddRange(inner.Statements);
            else if (rest is not null) stmts.Add(rest);
            return new IrBlock(Locations.From(c), stmts.ToImmutable());
        }

        if (BlockOf(syntax) is { } block)
        {
            var lowered = lowerer.Lower(block);
            // R26.2. The cells a `return` inside a loop is kept in, ahead of everything.
            if (lowerer.ReturnsInLoop && lowered is IrBlock b)
                return b with { Statements = [.. lowerer.ReturnCells(b.Loc), .. b.Statements] };
            return lowered;
        }
        if (ArrowOf(syntax) is { } arrow)
            return lowerer.LowerArrow(arrow);
        return null;
    }

    /// <summary>
    /// R4.12d. The declared field initialisers of the constructor's own class, in
    /// declaration order, each as the assignment `this.f = e` it stands for. C# runs them
    /// ahead of the constructor body and pal-csharp emits them there, so the constructor
    /// R4.12 reads is the one C# actually runs.
    /// </summary>
    private static IEnumerable<IrStmt> FieldInitialisers(
        ConstructorDeclarationSyntax ctor, StmtLowerer lowerer)
    {
        if (ctor.Parent is not TypeDeclarationSyntax type) yield break;

        foreach (var field in type.Members.OfType<FieldDeclarationSyntax>())
        {
            if (field.Modifiers.Any(m => m.IsKind(SyntaxKind.StaticKeyword)
                                      || m.IsKind(SyntaxKind.ConstKeyword))) continue;

            foreach (var v in field.Declaration.Variables)
            {
                if (v.Initializer is not { } init) continue;
                var loc = Locations.From(init);
                yield return new IrAssign(loc,
                    new IrField(loc, new IrVar(loc, Names.This), v.Identifier.ValueText),
                    lowerer.Expressions.Lower(init.Value));
            }
        }
    }

    private sealed record Specs(
        ImmutableArray<IrExpr> Requires,
        ImmutableArray<IrExpr> Ensures,
        ImmutableArray<IrExpr> Preserves,
        IrExpr? Decreases)
    {
        public ImmutableArray<IrThrows> Throws { get; init; } = [];
        public ImmutableArray<(string At, IrThrows Throws)> AtThrows { get; init; } = [];
    }

    // R32.13. The view a clause is `At`, and the one a replica is lowered at, may be symbols
    // of different compilations (a body is bound in one of its own).
    private static bool SameView(INamedTypeSymbol a, INamedTypeSymbol b) =>
        a.OriginalDefinition.ToDisplayString() == b.OriginalDefinition.ToDisplayString();

    private static Specs ReadSpecs(
        IMethodSymbol symbol, ISymbol declaration, WellKnown known,
        ImmutableDictionary<string, BoundSpec> bound, DiagnosticBag diagnostics,
        BorrowContext? borrow = null, INamedTypeSymbol? atView = null)
    {
        var requires = ImmutableArray.CreateBuilder<IrExpr>();
        var ensures = ImmutableArray.CreateBuilder<IrExpr>();
        var preserves = ImmutableArray.CreateBuilder<IrExpr>();
        IrExpr? decreases = null;

        foreach (var (attribute, index, _) in SpecAttributes(declaration, known))
        {
            var key = $"{Naming.Of(symbol)}_{index}";
            // R32.13. A member's own contract is its clauses without `At`; its replica at a
            // view has exactly the clauses `At` that view.
            var clauseAt = attribute.NamedArguments.FirstOrDefault(a => a.Key == "At").Value.Value as INamedTypeSymbol;
            if (atView is null ? clauseAt is not null
                : clauseAt is null || !SameView(clauseAt, atView))
                continue;
            if (!bound.TryGetValue(key, out var spec)) continue;

            var lowerer = new ExprLowerer(spec.Model, known, diagnostics, specPosition: true)
                { ContextNames = ContextNames(symbol, spec.Model.Compilation, known), Borrow = borrow,
                  OpenFields = OpenFields(symbol, known),
                  SnapshotResult = RefSnapshots.IsSnapshot(symbol, spec.Model.Compilation) &&
                                   known.MapType(symbol.ReturnType) is { } resultOf ? new IrOptionType(resultOf) : null,
                  DeclaredResult = symbol.ReturnsVoid ? null : known.MapType(symbol.ReturnType) };
            var expr = lowerer.Lower(spec.Expression);

            var cls = attribute.AttributeClass;
            if (Same(cls, known.RequiresAttribute)) requires.Add(expr);
            else if (Same(cls, known.EnsuresAttribute)) ensures.Add(expr);
            else if (Same(cls, known.PreservesAttribute) || Same(cls, known.PreservesValueAttribute))
                preserves.Add(expr);
            else if (Same(cls, known.DecreasesAttribute)) decreases = expr;
        }

        var throws = ImmutableArray.CreateBuilder<IrThrows>();
        var atThrows = ImmutableArray.CreateBuilder<(string, IrThrows)>();
        var throwsIndex = 0;
        foreach (var attribute in declaration.GetAttributes())
        {
            if (!Same(attribute.AttributeClass, known.ThrowsAttribute)) continue;
            var k = throwsIndex++;
            var aloc = Locations.From(attribute.ApplicationSyntaxReference?.GetSyntax().GetLocation()
                                      ?? Location.None);
            if (attribute.ConstructorArguments is not [{ Value: ITypeSymbol t }, ..] ||
                known.MapType(t) is not IrExnType type)
            {
                diagnostics.Error("PALCS0615", aloc,
                    "The type a `[Throws]` names must be `System.Exception` or an exception class " +
                    "the program declares (doc/translation.md R19.2).");
                continue;
            }
            if (!bound.TryGetValue($"{Naming.Of(symbol)}_throws_{k}", out var spec)) continue;
            var when = new ExprLowerer(spec.Model, known, diagnostics, specPosition: true)
                { ContextNames = ContextNames(symbol, spec.Model.Compilation, known), Borrow = borrow }
                .Lower(spec.Expression);
            var clause = new IrThrows(aloc, type, when is IrLiteral { Value: true } ? null : when);
            // R27.57. A clause for the replica at a subclass is not the member's own.
            var throwsAt = attribute.NamedArguments.FirstOrDefault(a => a.Key == "At").Value.Value as INamedTypeSymbol;
            // R32.13. At a view, only the clauses `At` it are the replica's.
            if (atView is not null)
            {
                if (throwsAt is not null && SameView(throwsAt, atView))
                    throws.Add(clause);
            }
            else if (throwsAt is not null)
                atThrows.Add((throwsAt.Name, clause));
            else
                throws.Add(clause);
        }

        return new Specs(requires.ToImmutable(), ensures.ToImmutable(), preserves.ToImmutable(), decreases)
        {
            Throws = throws.ToImmutable(),
            AtThrows = atThrows.ToImmutable(),
        };
    }

    /// <summary>R27.23. The receiver's instance fields, for an <c>[Open]</c> method's contract.</summary>
    private static ImmutableHashSet<string> OpenFields(IMethodSymbol symbol, WellKnown known) =>
        !symbol.IsStatic && Declarations.Has(symbol, known.OpenAttribute) && symbol.ContainingType is { } holder
            ? holder.GetMembers().OfType<IFieldSymbol>().Where(f => !f.IsStatic && !f.IsConst)
                .Select(f => f.Name).ToImmutableHashSet()
            : [];

    /// <summary>
    /// R20.12. The receiver fields a contract of <paramref name="symbol"/> names, by name:
    /// its context fields, and the class's <c>static readonly</c> fields the contract
    /// mentions. Each is bound by a parameter of the spec shim, which lives outside the
    /// class, so a private field binds too. A parameter of the method shadows a field.
    /// </summary>
    private static ImmutableDictionary<string, ISymbol> ContextNames(
        IMethodSymbol symbol, Compilation compilation, WellKnown known)
    {
        if (!Declarations.IsReceiverFree(symbol, known)) return ImmutableDictionary<string, ISymbol>.Empty;
        var result = ImmutableDictionary.CreateBuilder<string, ISymbol>();
        foreach (var f in Declarations.ContextFields(symbol.ContainingType, compilation, known))
            result[f.Name] = f;
        foreach (var f in Declarations.ContractStatics(symbol, known))
            result[f.Name] = f;
        foreach (var p in symbol.Parameters) result.Remove(p.Name);
        return result.ToImmutable();
    }

    private static ImmutableArray<IrParam> LowerParameters(
        IMethodSymbol symbol, SemanticModel model, WellKnown known, DiagnosticBag diagnostics)
    {
        var result = ImmutableArray.CreateBuilder<IrParam>();
        foreach (var p in symbol.Parameters)
        {
            var loc = p.Locations.Length > 0 ? Locations.From(p.Locations[0]) : IrLoc.None;
            var isGhost = known.IsGhost(p.Type);
            var declared = isGhost ? ((INamedTypeSymbol)p.Type).TypeArguments[0] : p.Type;
            if (Declarations.Has(p, known.ExactlyAttribute))
            {
                if (ExactParameter(p, model.Compilation, known) is not { } exact)
                {
                    diagnostics.Error("PALCS0713", loc,
                        $"`[Exactly]` on `{p.Name}` names no class translated at its exact type (R27.1) " +
                        $"that converts to `{p.Type}` (doc/translation.md R27.46).");
                    continue;
                }
                declared = exact;
            }
            var type = known.MapType(declared);
            if (type is null)
            {
                diagnostics.Unsupported(loc, $"The parameter type `{p.Type}`");
                continue;
            }

            // R27.28. `[AllowNull]` on a non-nullable reference parameter says null is passed
            // anyway: its type is the nullable one, so no caller is asked to prove what the
            // program does not hold.
            if (type is IrClassType { Nullable: false } nk && p.GetAttributes().Any(a =>
                    a.AttributeClass?.ToDisplayString() == "System.Diagnostics.CodeAnalysis.AllowNullAttribute"))
                type = nk with { Nullable = true };

            // R20.13. A written specification-type parameter is passed by reference.
            var mode = Declarations.IsWritten(p, model.Compilation, known) ? ParamMode.Ref : Declarations.ModeOf(p);
            result.Add(new IrParam(loc, p.Name, type, mode)
            {
                IsGhost = isGhost,
                Callback = ExprLowerer.CallbackOf(p, known, diagnostics),
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
            SyntaxNode syntax, SemanticModel model, WellKnown known, StmtLowerer lowerer,
            bool lowerRest = true)
    {
        if (BlockOf(syntax) is not { } block)
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

        if (leading == 0 || !lowerRest) return (requires.ToImmutable(), ensures.ToImmutable(), null);

        var body = new IrBlock(Locations.From(block),
            [.. block.Statements.Skip(leading).Select(lowerer.Lower)]);
        return (requires.ToImmutable(), ensures.ToImmutable(), body);
    }
}
