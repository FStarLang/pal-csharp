using System.Collections.Immutable;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;

namespace Pal.Compiler.Frontend;

/// <summary>
/// Builds a <see cref="CSharpCompilation"/> for the user's sources with
/// <c>Pal.Annotations</c> referenced. pal-csharp refuses to translate a program
/// that does not compile: the whole point of the design is that annotated C# is
/// ordinary C#.
/// </summary>
public static class Loader
{
    /// <summary>The <c>PAL</c> preprocessor symbol, which makes annotations live.</summary>
    public const string PalSymbol = "PAL";

    /// <param name="references">R36.2. The compilations of the units this one references.</param>
    /// <param name="internalsVisibleTo">R36.2. The units that reference this one: each sees its
    /// <c>internal</c> declarations, as code of one assembly does.</param>
    public static CSharpCompilation Create(
        IEnumerable<string> sourcePaths, string assemblyName = "PalInput", bool nullable = true,
        bool preview = false, bool allowUnsafe = false,
        IEnumerable<CSharpCompilation>? references = null, IEnumerable<string>? internalsVisibleTo = null)
    {
        var parseOptions = new CSharpParseOptions(
            preview ? LanguageVersion.Preview : LanguageVersion.Latest,
            preprocessorSymbols: [PalSymbol]);

        var trees = sourcePaths.Select(p =>
            CSharpSyntaxTree.ParseText(
                SourceText(p), parseOptions, path: p)).ToImmutableArray();

        // Last, so that the first tree is still the user's (SpecBinder reads its options).
        var clients = internalsVisibleTo?.ToList() ?? [];
        if (clients.Count > 0)
            trees = trees.Add(CSharpSyntaxTree.ParseText(
                string.Concat(clients.Select(c =>
                    $"[assembly: System.Runtime.CompilerServices.InternalsVisibleTo(\"{c}\")]\n")),
                parseOptions, path: InternalsTreePath));

        var units = references?.ToList() ?? [];
        var compilation = CSharpCompilation.Create(
            assemblyName,
            trees,
            [.. ReferenceSet(), .. units.Select(r => (MetadataReference)r.ToMetadataReference())],
            new CSharpCompilationOptions(
                OutputKind.DynamicallyLinkedLibrary,
                                nullableContextOptions: nullable
                    ? NullableContextOptions.Enable
                    : NullableContextOptions.Disable,
                allowUnsafe: allowUnsafe));
        if (units.Count == 0) return compilation;
        // R36.2. A referenced unit's public types are metadata here, as the framework's own
        // copies are (`List<T>`), so the unit's must be made to win the way source would.
        var names = Units.DeclaredTypeNames(Units.WithReferences(compilation).Skip(1));
        if (Units.WithBinderFlags(compilation.Options, "IgnoreCorLibraryDuplicatedTypes") is { } options)
            compilation = compilation.WithOptions(options);
        return compilation.WithReferences(Units.HidingDuplicates(compilation, compilation.References, names, anyAccessibility: false));
    }

    private static Microsoft.CodeAnalysis.Text.SourceText SourceText(string path) =>
        Microsoft.CodeAnalysis.Text.SourceText.From(File.ReadAllText(path), System.Text.Encoding.UTF8);

    /// <summary>
    /// References: the shared framework plus <c>Pal.Annotations</c>, and nothing else.
    /// Restricting the set to the framework directory matters — the tool's own
    /// assemblies live alongside it on the trusted-platform list, and referencing
    /// <c>Pal.Compiler</c> would make <c>Pal</c> resolve to a namespace and shadow the
    /// <c>PalLang.Pal</c> intrinsics class in every user program.
    /// </summary>
    /// <summary>R36.2. The synthesized tree that opens a referenced unit's internals to its clients.</summary>
    public const string InternalsTreePath = "<pal-unit-internals>.g.cs";

    /// <remarks>
    /// One set, shared by every compilation of a run: a unit referenced as a compilation
    /// is seen by its client as the very symbols it declares only when the two were built
    /// over the same framework metadata. Otherwise Roslyn retargets them, and a symbol read
    /// off a referenced unit's own syntax would not be equal to the one the client binds.
    /// </remarks>
    public static ImmutableArray<MetadataReference> ReferenceSet() => SharedReferences.Value;

    private static readonly Lazy<ImmutableArray<MetadataReference>> SharedReferences = new(BuildReferenceSet);

    private static ImmutableArray<MetadataReference> BuildReferenceSet()
    {
        var annotations = typeof(PalLang.RequiresAttribute).Assembly.Location;
        var framework = Path.GetDirectoryName(typeof(object).Assembly.Location);
        var tpa = (string?)AppContext.GetData("TRUSTED_PLATFORM_ASSEMBLIES") ?? "";

        var paths = tpa
            .Split(Path.PathSeparator, StringSplitOptions.RemoveEmptyEntries)
            .Where(p => framework is not null &&
                        string.Equals(Path.GetDirectoryName(p), framework, StringComparison.OrdinalIgnoreCase))
            .Append(annotations)
            .Where(p => p.EndsWith(".dll", StringComparison.OrdinalIgnoreCase) && File.Exists(p))
            .Distinct(StringComparer.OrdinalIgnoreCase);

        return [.. paths.Select(p => (MetadataReference)MetadataReference.CreateFromFile(p))];
    }
}
