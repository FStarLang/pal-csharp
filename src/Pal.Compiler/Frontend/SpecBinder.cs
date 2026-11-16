using System.Collections.Immutable;
using System.Text;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using Pal.Compiler.Diagnostics;

namespace Pal.Compiler.Frontend;

/// <summary>A binder that must be in scope while a spec string is bound.</summary>
public sealed record SpecParam(string Name, ITypeSymbol Type);

/// <summary>
/// One specification written as a string in an attribute — a <c>[Requires]</c>,
/// <c>[Ensures]</c>, <c>[Preserves]</c>, <c>[Decreases]</c> or <c>[Refine]</c>.
/// </summary>
public sealed record SpecSite(
    string Key,
    string Text,
    Location Location,
    ImmutableArray<SpecParam> Parameters,
    ImmutableArray<string> Usings)
{
    /// <summary>
    /// R14.2b. The enclosing method's type parameters. A specification is bound in the
    /// method's scope, and that scope includes them: <c>[Ensures("Result == a[i]")]</c>
    /// on a method over <c>T[]</c> cannot bind unless the shim is generic in <c>T</c>
    /// too. The shim needs no constraints because R14.1 admits none.
    /// </summary>
    public ImmutableArray<string> TypeParameters { get; init; } = [];

    /// <summary>
    /// R24.17. The contract is of a <c>private</c> member: its only clients are inside the
    /// declaring type, which sees that type's private members.
    /// </summary>
    public bool Private { get; init; }

    /// <summary>Name of the generated shim method; also the lookup key.</summary>
    public string ShimName => SpecBinder.ShimMethodPrefix + Key;
}

/// <summary>A successfully bound spec: real syntax, with a real semantic model behind it.</summary>
public sealed record BoundSpec(ExpressionSyntax Expression, SemanticModel Model, SpecSite Site);

/// <summary>
/// Binds attribute spec strings by <b>generating a shim compilation unit</b> and
/// letting Roslyn compile it, rather than by speculative binding.
///
/// <para>
/// This is deliberate. Speculative binding (<c>GetSpeculativeSymbolInfo</c>,
/// <c>TryGetSpeculativeSemanticModel</c>) resolves a node against a position but reports
/// no diagnostics of its own: a mistyped spec comes back as a null symbol with no
/// explanation. A shim, being ordinary C#, gets Roslyn's full error reporting —
/// overload resolution failures, type mismatches, inaccessible members — for free.
/// </para>
/// <para>
/// It is also possible only because pal-csharp's string specs attach to
/// <em>declarations</em>. They never need method-body locals in scope; loop invariants,
/// which do, are written as typed <c>Pal.Invariant(...)</c> calls and are bound by the
/// ordinary semantic model. So a shim whose parameters are the enclosing method's
/// parameters reproduces exactly the scope a string spec is entitled to see.
/// </para>
/// <para>
/// Spans are carried back to the original file with C#'s line-span directive
/// (<c>#line (a,b)-(c,d) offset "file"</c>), the same mechanism Razor uses, so a
/// diagnostic lands inside the string literal in the user's source.
/// </para>
/// </summary>
public static class SpecBinder
{
    public const string ShimNamespace = "__PalSpecShims";
    private const string ShimPrefix = "__PalSpecShim";

    /// <summary>Prefix of every generated shim method; see <see cref="SpecSite.ShimName"/>.</summary>
    public const string ShimMethodPrefix = "__pal_";

    /// <summary>The shim parameter standing for a method's returned value.</summary>
    public const string ResultParameter = "Result";

    /// <summary>
    /// Adds shim trees to <paramref name="compilation"/>, compiles them, reports any
    /// errors against the original source, and returns the bound specs.
    /// </summary>
    public static ImmutableDictionary<string, BoundSpec> Bind(
        ref CSharpCompilation compilation,
        IReadOnlyList<SpecSite> sites,
        DiagnosticBag diagnostics)
    {
        if (sites.Count == 0) return ImmutableDictionary<string, BoundSpec>.Empty;

        var options = (CSharpParseOptions)compilation.SyntaxTrees[0].Options;
        var result = ImmutableDictionary.CreateBuilder<string, BoundSpec>();

        // One tree per distinct set of usings: `using` directives are file-scoped, and
        // unioning them across unrelated methods would invent ambiguities that do not
        // exist in the user's program.
        var groups = sites
            .GroupBy(s => string.Join("\u0000", s.Usings))
            .Select((g, i) => (Index: i, Sites: g.ToImmutableArray(), Usings: g.First().Usings))
            .ToList();

        var trees = new List<(SyntaxTree Tree, ImmutableArray<SpecSite> Sites, Dictionary<int, SpecSite> Map)>();
        foreach (var (index, groupSites, usings) in groups)
        {
            var (text, map) = BuildShim(index, usings, groupSites);
            var path = $"{ShimPrefix}{index}.g.cs";
            var tree = CSharpSyntaxTree.ParseText(
                Microsoft.CodeAnalysis.Text.SourceText.From(text, Encoding.UTF8), options, path: path);
            trees.Add((tree, groupSites, map));
        }

        // R24.3. An `[Invariant]` is about the representation, so like `[Model]` (R4.10b)
        // it is exempt from the client's view: its shim's parameters are the fields, and a
        // field may be at a private nested type (`HashSet<T>.Entry[]`). The strict
        // compilation still reports every error, less an inaccessibility inside an
        // invariant's shim; the specs are then bound against a compilation that ignores
        // accessibility, which only ever differs from the strict one there.
        var privateShims = new HashSet<string>(sites.Where(s => s.Private).Select(s => s.ShimName));
        var strict = compilation.AddSyntaxTrees(trees.Select(t => t.Tree));
        var exempt = false;
        foreach (var (tree, _, _) in trees)
            foreach (var d in strict.GetSemanticModel(tree).GetDiagnostics())
                if (d.Severity == DiagnosticSeverity.Error && IsInvariantInaccessible(d, privateShims)) exempt = true;
        compilation = exempt && IgnoringAccessibility(compilation) is { } lax
            ? lax.AddSyntaxTrees(trees.Select(t => t.Tree))
            : strict;

        foreach (var (tree, groupSites, map) in trees)
        {
            var model = compilation.GetSemanticModel(tree);

            foreach (var d in strict.GetSemanticModel(strict.SyntaxTrees.First(t => t.FilePath == tree.FilePath)).GetDiagnostics())
            {
                if (d.Severity != DiagnosticSeverity.Error) continue;
                if (IsInvariantInaccessible(d, privateShims)) continue;
                var (code, message) = Remap(d);
                diagnostics.Error(code, MapBack(d.Location, map, groupSites), message);
            }

            // R18.3: keyed by a name R2.1a intends to be unique, and grouped rather than
            // added so that a name it failed to make unique is PALCS0501's to report and
            // not a stack trace out of a pass that runs before any check.
            var byName = tree.GetRoot()
                .DescendantNodes()
                .OfType<MethodDeclarationSyntax>()
                .GroupBy(m => m.Identifier.ValueText)
                .ToDictionary(g => g.Key, g => g.First());

            foreach (var site in groupSites)
            {
                if (!byName.TryGetValue(site.ShimName, out var method)) continue;
                var expr = method.DescendantNodes().OfType<ReturnStatementSyntax>()
                    .Select(r => r.Expression).FirstOrDefault();
                if (expr is not null) result[site.Key] = new BoundSpec(expr, model, site);
            }
        }

        return result.ToImmutable();
    }

    private static bool IsInvariantInaccessible(Diagnostic d, HashSet<string> privateShims) =>
        d.Id == "CS0122" && d.Location.SourceTree is { } t &&
        t.GetRoot().FindNode(d.Location.SourceSpan).AncestorsAndSelf()
            .OfType<MethodDeclarationSyntax>().FirstOrDefault() is { } m &&
        (m.Identifier.ValueText.Contains("_invariant_") || privateShims.Contains(m.Identifier.ValueText));

    /// <summary>
    /// R24.3. Roslyn's own switch for binding without accessibility checks (the one its
    /// debugger evaluator uses) is internal, so it is reached by reflection; when it is
    /// absent the strict compilation is used and the CS0122 surfaces as a binding failure.
    /// </summary>
    private static CSharpCompilation? IgnoringAccessibility(CSharpCompilation c)
    {
        var units = c.References.OfType<CompilationReference>().Select(r => r.Compilation).ToList();
        // R36.2. Corlib's duplicates of a referenced unit's types lose to the unit's.
        var options = units.Count > 0
            ? Units.WithBinderFlags(c.Options, "IgnoreAccessibility", "IgnoreCorLibraryDuplicatedTypes")
            : Units.WithBinderFlags(c.Options, "IgnoreAccessibility");
        if (options is null) return null;
        // Ignoring accessibility also makes every internal type of every referenced
        // assembly a candidate, and two framework assemblies declaring the same internal
        // name (`System.Collections.ThrowHelper`) then make a program name ambiguous that
        // the strict compilation resolves. Only the references the program uses are kept.
        var used = c.GetUsedAssemblyReferences();
        var kept = c.References.Where(r => used.Contains(r));
        // R36.2. A referenced unit's declarations are metadata to this compilation, not
        // source, so they no longer win over a framework internal of the same name the way
        // its own would; another framework assembly declaring one is hidden.
        if (units.Count > 0)
            kept = Units.HidingDuplicates(c, kept, Units.DeclaredTypeNames(units), anyAccessibility: true).ToList();
        return c.WithOptions(options).WithReferences(kept);
    }

    /// <summary>
    /// R4.10a and R4.10b. Two C# errors are, inside a spec string, always the same two
    /// mistakes about the shim, and Roslyn's wording describes the shim rather than the
    /// contract the user wrote — it talks about a static method the user has never seen.
    /// Both are remapped to a message phrased in terms of the annotation surface. Every
    /// other error is genuinely about the user's expression and is reported verbatim,
    /// because Roslyn says it better than we would.
    /// </summary>
    private static (string Code, string Message) Remap(Diagnostic d) => d.Id switch
    {
        // CS0026: 'this' is not valid in a static method. R4.10a: the receiver of a
        // contract is an ordinary parameter named `this`, so it is written `@this`.
        "CS0026" => ("PALCS0526",
            "in specification: write `@this` for the receiver. A contract is bound as a "
            + "static method, so a bare `this` does not resolve; `@this` is the verbatim "
            + "identifier naming the receiver parameter (R4.10a)."),

        // CS0122: inaccessible. R4.10b: the shim is a separate namespace, so a contract
        // sees only what a client sees.
        "CS0122" => ("PALCS0525",
            $"in specification: {d.GetMessage()} A contract may name only members a client "
            + "could name, so a `[Spec]` member used in one must be at least `internal`. "
            + "`[Model]` is exempt — it is read inside the class, where the fields are "
            + "visible (R4.10b)."),

        _ => ("PALCS0100", $"in specification: {d.GetMessage()}"),
    };

    /// <summary>
    /// Emits one shim method per spec site. The spec text is placed alone on a line so
    /// that a line-span directive can map it back verbatim.
    /// </summary>
    private static (string Text, Dictionary<int, SpecSite> LineMap) BuildShim(
        int index, ImmutableArray<string> usings, ImmutableArray<SpecSite> sites)
    {
        var sb = new StringBuilder();
        var lineMap = new Dictionary<int, SpecSite>();

        sb.AppendLine("// <auto-generated/> pal-csharp specification shim.");
        sb.AppendLine("#nullable disable");
        sb.AppendLine("#pragma warning disable");
        foreach (var u in usings) sb.AppendLine(u);
        sb.AppendLine($"namespace {ShimNamespace};");
        sb.AppendLine($"static class __C{index}");
        sb.AppendLine("{");

        foreach (var site in sites)
        {
            sb.Append("    internal static object ").Append(site.ShimName);
            if (site.TypeParameters.Length > 0)
                sb.Append('<').Append(string.Join(", ", site.TypeParameters)).Append('>');
            sb.Append('(');
            sb.Append(string.Join(", ", site.Parameters.Select(RenderParam)));
            sb.AppendLine(")");
            sb.AppendLine("    {");
            sb.AppendLine("        return");

            // The spec text is indented by exactly `ContentOffset` characters, which is
            // also the directive's character offset, so column p of the spec text maps
            // to column p of the original string literal's contents.
            sb.AppendLine(LineDirective(site));
            lineMap[CountLines(sb)] = site;
            sb.Append(new string(' ', ContentOffset)).AppendLine(site.Text);
            sb.AppendLine("#line default");
            sb.AppendLine("        ;");
            sb.AppendLine("    }");
        }

        sb.AppendLine("}");
        // The shim is the only artefact a spec-binding diagnostic is really *about*: a
        // `PALCS0100` names a C# error at a position inside a generated file the user
        // never sees, and mapping it back by eye is guesswork. `PALCS_DUMP_SHIM=1` prints
        // the file. It earned its place finding that `using static` cannot name an open
        // generic type (R15.1), which surfaced as an unresolved `T` in an unrelated
        // `[Ensures]` several members away.
        if (System.Environment.GetEnvironmentVariable("PALCS_DUMP_SHIM") is not null)
            System.Console.Error.WriteLine(sb.ToString());
        return (sb.ToString(), lineMap);
    }

    private static string RenderParam(SpecParam p) =>
        $"{RenderType(p.Type)} @{p.Name}";

    /// <summary>
    /// R17.1, in the shim. A span parameter is declared to the shim as the **array** it
    /// denotes. Two things make this the right rendering rather than a shortcut. It is what
    /// R17.1 says the span *is*, so `Contents(a)` binds to the same `Seq&lt;T&gt;` either
    /// way and no spec term changes. And it is what makes a quantified contract writable at
    /// all: `Span&lt;T&gt;` is a `ref struct`, so a shim whose parameter kept that type
    /// would reject every `Forall((int k) =&gt; … Contents(a)[k] …)` with CS9108, "cannot
    /// use parameter that has ref-like type inside a lambda". The array has no such rule.
    /// </summary>
    private static string RenderType(ITypeSymbol type) =>
        type is INamedTypeSymbol { MetadataName: "Span`1" or "ReadOnlySpan`1" } span &&
        span.ContainingNamespace is { Name: "System", ContainingNamespace.IsGlobalNamespace: true }
            ? RenderType(span.TypeArguments[0]) + "[]"
            : type.ToDisplayString(SymbolDisplayFormat.FullyQualifiedFormat);

    /// <summary>
    /// Characters of the shim line to skip before the spec text begins. A line-span
    /// directive's offset must be at least 1 (an offset of 0 is rejected, CS8938), so
    /// the spec text is indented by that much and the two cancel out exactly.
    /// </summary>
    private const int ContentOffset = 1;

    private static string LineDirective(SpecSite site)
    {
        // `site.Location` is the span of the string literal's *contents*, so the
        // directive's start position is where the user's first spec character sits.
        var span = site.Location.GetLineSpan();
        var start = span.StartLinePosition;
        var end = span.EndLinePosition;
        return $"#line ({start.Line + 1}, {start.Character + 1}) - " +
               $"({end.Line + 1}, {end.Character + 1}) {ContentOffset} \"{span.Path.Replace("\\", "\\\\")}\"";
    }

    /// <summary>
    /// The location of a string literal's <em>contents</em>, excluding its delimiters.
    /// Diagnostics are reported against this, so an error inside a spec squiggles the
    /// offending sub-expression rather than the whole attribute.
    /// </summary>
    public static Location ContentLocation(ExpressionSyntax expression)
    {
        if (expression is not LiteralExpressionSyntax literal) return expression.GetLocation();

        var text = literal.Token.Text;
        var open = text.StartsWith("@\"", StringComparison.Ordinal) ? 2
            : text.StartsWith("\"", StringComparison.Ordinal) ? 1
            : 0;
        if (open == 0) return expression.GetLocation();

        var span = literal.Token.Span;
        var close = text.EndsWith("\"", StringComparison.Ordinal) ? 1 : 0;
        return Location.Create(
            literal.SyntaxTree,
            Microsoft.CodeAnalysis.Text.TextSpan.FromBounds(
                span.Start + open, Math.Max(span.Start + open, span.End - close)));
    }

    private static int CountLines(StringBuilder sb)
    {
        var n = 1;
        for (var i = 0; i < sb.Length; i++) if (sb[i] == '\n') n++;
        return n;
    }

    /// <summary>
    /// Turns a diagnostic on the shim into one on the user's source. The line-span
    /// directive normally does this for us; the line map is the fallback for the case
    /// where the error lands on shim scaffolding rather than on the spec text.
    /// </summary>
    private static Ir.IrLoc MapBack(
        Location location, Dictionary<int, SpecSite> lineMap, ImmutableArray<SpecSite> sites)
    {
        var mapped = location.GetMappedLineSpan();
        if (!mapped.Path.StartsWith(ShimPrefix, StringComparison.Ordinal))
            return Locations.From(mapped);

        if (lineMap.TryGetValue(location.GetLineSpan().StartLinePosition.Line + 1, out var site))
            return Locations.From(site.Location);

        return sites.Length > 0 ? Locations.From(sites[0].Location) : Ir.IrLoc.None;
    }
}

/// <summary>Conversions between Roslyn locations and <see cref="Ir.IrLoc"/>.</summary>
public static class Locations
{
    public static Ir.IrLoc From(FileLinePositionSpan span) => new(
        span.Path,
        span.StartLinePosition.Line + 1,
        span.StartLinePosition.Character + 1,
        span.EndLinePosition.Line + 1,
        span.EndLinePosition.Character + 1);

    /// <summary>
    /// The <em>mapped</em> span, so that a diagnostic raised while binding a
    /// specification lands inside the string literal the user wrote rather than in the
    /// generated shim (see <see cref="SpecBinder"/>'s <c>#line</c> directives).
    /// </summary>
    public static Ir.IrLoc From(Location location) => From(location.GetMappedLineSpan());

    public static Ir.IrLoc From(SyntaxNode node) => From(node.GetLocation());

    public static Ir.IrLoc From(SyntaxToken token) => From(token.GetLocation());
}
