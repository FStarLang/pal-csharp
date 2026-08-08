using System.Collections.Immutable;
using System.Text;
using System.Text.Json;
using Pal.Compiler.Ir;

namespace Pal.Compiler.Diagnostics;

public enum Severity { Error, Warning, Info }

/// <summary>
/// A pal-csharp diagnostic. Carries a real source span — including spans *inside*
/// a spec string literal — so that editors and `diagnostics.json` agree.
/// </summary>
public sealed record PalDiagnostic(
    Severity Severity,
    string Id,
    string Message,
    IrLoc Location)
{
    public override string ToString() =>
        $"{Location.File}({Location.Line},{Location.Column}): " +
        $"{Severity.ToString().ToLowerInvariant()} {Id}: {Message}";
}

/// <summary>Collects diagnostics across all passes.</summary>
public sealed class DiagnosticBag
{
    private readonly List<PalDiagnostic> _items = [];

    public ImmutableArray<PalDiagnostic> Items => [.. _items];

    public bool HasErrors => _items.Any(d => d.Severity == Severity.Error);

    public void Add(PalDiagnostic d) => _items.Add(d);

    public void Error(string id, IrLoc loc, string message) =>
        Add(new PalDiagnostic(Severity.Error, id, message, loc));

    public void Warning(string id, IrLoc loc, string message) =>
        Add(new PalDiagnostic(Severity.Warning, id, message, loc));

    /// <summary>
    /// The one diagnostic that says "this construct is outside the supported subset".
    /// Kept as a single helper so the message shape is uniform and greppable.
    /// </summary>
    public void Unsupported(IrLoc loc, string construct, string? hint = null) =>
        Error("PALCS0001", loc,
            hint is null
                ? $"{construct} is not supported by pal-csharp."
                : $"{construct} is not supported by pal-csharp. {hint}");

    /// <summary>
    /// R17.5. A span that is not the whole of an array. This is its own id rather than
    /// `PALCS0001` because it is not a gap in effort: R17.1 identifies a span with the
    /// array it denotes, and everything named here would break the identification -- a
    /// window has a length of its own (so R17.3 would be wrong), a base of its own (R17.4),
    /// and an owner who owes it back (R4.9). Naming §17 in the message says which question
    /// is open rather than implying the construct is unverifiable, which it is not.
    /// </summary>
    public void SpanWindow(IrLoc loc, string construct) =>
        Error("PALCS0590", loc,
            $"{construct} is not supported by pal-csharp: it makes a span that is not the " +
            "whole of an array. A span is translated as the array it denotes (§17, R17.1), " +
            "which holds only for a whole-array span. Pass the array and an index range as " +
            "separate parameters, or index the array directly.");

    public string Render()
    {
        var sb = new StringBuilder();
        foreach (var d in _items) sb.AppendLine(d.ToString());
        return sb.ToString();
    }

    /// <summary>LSP-compatible output, matching PAL's `diagnostics.json`.</summary>
    public string ToJson() => JsonSerializer.Serialize(
        _items.Select(d => new
        {
            severity = d.Severity.ToString().ToLowerInvariant(),
            code = d.Id,
            message = d.Message,
            file = d.Location.File,
            range = new
            {
                start = new { line = d.Location.Line - 1, character = d.Location.Column - 1 },
                end = new { line = d.Location.EndLine - 1, character = d.Location.EndColumn - 1 },
            },
        }),
        new JsonSerializerOptions { WriteIndented = true });
}
