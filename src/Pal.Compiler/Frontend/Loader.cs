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

    public static CSharpCompilation Create(
        IEnumerable<string> sourcePaths, string assemblyName = "PalInput", bool nullable = true,
        bool preview = false, bool allowUnsafe = false)
    {
        var parseOptions = new CSharpParseOptions(
            preview ? LanguageVersion.Preview : LanguageVersion.Latest,
            preprocessorSymbols: [PalSymbol]);

        var trees = sourcePaths.Select(p =>
            CSharpSyntaxTree.ParseText(
                SourceText(p), parseOptions, path: p)).ToImmutableArray();

        return CSharpCompilation.Create(
            assemblyName,
            trees,
            ReferenceSet(),
            new CSharpCompilationOptions(
                OutputKind.DynamicallyLinkedLibrary,
                                nullableContextOptions: nullable
                    ? NullableContextOptions.Enable
                    : NullableContextOptions.Disable,
                allowUnsafe: allowUnsafe));
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
    public static ImmutableArray<MetadataReference> ReferenceSet()
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
