using System.Collections.Immutable;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;

namespace Pal.Compiler.Frontend;

/// <summary>
/// §36. Verification units. A unit is translated in a compilation of its own, which refers
/// to the compilations of the units it references (R36.2). Its frontend still reads the
/// declarations and bodies of those units — a callee's body, a class's subclasses — so
/// every question "which compilation is this syntax in" is answered here, over the unit and
/// everything it references, rather than over the unit alone.
/// </summary>
public static class Units
{
    /// <summary>The compilation and every compilation it references, transitively.</summary>
    public static IEnumerable<Compilation> WithReferences(Compilation compilation)
    {
        var seen = new HashSet<Compilation>();
        var work = new Stack<Compilation>();
        work.Push(compilation);
        while (work.Count > 0)
        {
            var c = work.Pop();
            if (!seen.Add(c)) continue;
            yield return c;
            foreach (var r in c.References.OfType<CompilationReference>())
                work.Push(r.Compilation);
        }
    }

    /// <summary>The compilation, of this one or of a unit it references, that <paramref name="tree"/> is in.</summary>
    public static Compilation? Owner(Compilation compilation, SyntaxTree tree) =>
        compilation.ContainsSyntaxTree(tree)
            ? compilation
            : WithReferences(compilation).FirstOrDefault(c => c.ContainsSyntaxTree(tree));

    /// <summary>Whether <paramref name="tree"/> is source of this unit or of one it references.</summary>
    public static bool Owns(this Compilation compilation, SyntaxTree tree) => Owner(compilation, tree) is not null;

    /// <summary>
    /// The semantic model of <paramref name="tree"/> in the compilation that owns it. A model
    /// can only be had from that compilation; the symbols it binds are the ones this
    /// compilation sees, because a referenced unit is referenced as its compilation (R36.2).
    /// </summary>
    public static SemanticModel Model(this Compilation compilation, SyntaxTree tree) =>
        (Owner(compilation, tree) ?? compilation).GetSemanticModel(tree);

    /// <summary>Whether <paramref name="symbol"/> is declared by a unit this compilation references.</summary>
    public static bool IsReferenced(this Compilation compilation, ISymbol symbol) =>
        symbol.DeclaringSyntaxReferences.Length > 0 &&
        symbol.DeclaringSyntaxReferences.All(r => !compilation.ContainsSyntaxTree(r.SyntaxTree) && compilation.Owns(r.SyntaxTree));

    /// <summary>The types declared in the sources of this unit and of every unit it references.</summary>
    public static IEnumerable<INamedTypeSymbol> SourceTypes(Compilation compilation) =>
        WithReferences(compilation).SelectMany(c =>
            c.GetSymbolsWithName(_ => true, SymbolFilter.Type).OfType<INamedTypeSymbol>());

    /// <summary>The metadata names of the top-level types declared by the given units.</summary>
    internal static ImmutableHashSet<string> DeclaredTypeNames(IEnumerable<Compilation> units) =>
        units.SelectMany(u => AllNamespaces(u.Assembly.GlobalNamespace).Prepend(u.Assembly.GlobalNamespace))
            .SelectMany(n => n.GetTypeMembers())
            .Select(t => t.ContainingNamespace.IsGlobalNamespace ? t.MetadataName : $"{t.ContainingNamespace.ToDisplayString()}.{t.MetadataName}")
            .ToImmutableHashSet();

    private static IEnumerable<INamespaceSymbol> AllNamespaces(INamespaceSymbol ns) =>
        ns.GetNamespaceMembers().SelectMany(n => AllNamespaces(n).Prepend(n));

    /// <summary>
    /// R36.2. A framework assembly other than corlib that declares one of <paramref name="names"/>
    /// (publicly, or at all when <paramref name="anyAccessibility"/>) is referenced behind an
    /// extern alias, so that the unit's declaration is the only one a program name finds.
    /// An alias rather than a dropped reference keeps the reference set, and with it the
    /// identity of every symbol, the same.
    /// </summary>
    internal static IEnumerable<MetadataReference> HidingDuplicates(
        Compilation c, IEnumerable<MetadataReference> references, ImmutableHashSet<string> names, bool anyAccessibility)
    {
        var corlib = c.ObjectType.ContainingAssembly;
        return references.Select(r =>
            r is CompilationReference || !r.Properties.Aliases.IsEmpty ||
            c.GetAssemblyOrModuleSymbol(r) is not IAssemblySymbol a ||
            SymbolEqualityComparer.Default.Equals(a, corlib) ||
            !names.Any(n => a.GetTypeByMetadataName(n) is { } t &&
                (anyAccessibility || t.DeclaredAccessibility == Accessibility.Public))
                ? r : r.WithAliases(["palcs_hidden"]));
    }

    /// <summary>
    /// <paramref name="options"/> with Roslyn's internal top-level binder flags set to
    /// <paramref name="flags"/>, reached by reflection (R24.3); null when this Roslyn has no
    /// such switch or no such flag.
    /// </summary>
    internal static CSharpCompilationOptions? WithBinderFlags(CSharpCompilationOptions options, params string[] flags)
    {
        var flagsType = typeof(CSharpCompilation).Assembly.GetType("Microsoft.CodeAnalysis.CSharp.BinderFlags");
        var with = typeof(CSharpCompilationOptions).GetMethod("WithTopLevelBinderFlags",
            System.Reflection.BindingFlags.NonPublic | System.Reflection.BindingFlags.Instance);
        if (flagsType is null || with is null || !flags.All(f => Enum.IsDefined(flagsType, f))) return null;
        var value = flags.Aggregate(0u, (acc, f) => acc | Convert.ToUInt32(Enum.Parse(flagsType, f)));
        return with.Invoke(options, [Enum.ToObject(flagsType, value)]) as CSharpCompilationOptions;
    }
}
