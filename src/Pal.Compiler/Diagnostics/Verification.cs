using System;
using System.Collections.Generic;
using System.Collections.Immutable;
using System.Linq;
using System.Text;

namespace Pal.Compiler.Diagnostics;

/// <summary>
/// A verification result, read back onto the C# it came from.
///
/// <para>
/// pal-csharp refuses what it cannot translate and says nothing about what it can. Whether
/// a translated program is <em>provable</em> is a question for Pulse, deliberately: a
/// checker that answered it would be a second, weaker prover, and the one place a rule
/// must never live is in two places at once. So the answer arrives from F*, and the job
/// left over is to say it in terms of the program the user wrote.
/// </para>
/// <para>
/// This type is the wire between the two halves — <c>palcs report</c> writes it, the
/// analyzer reads it — and it is deliberately a flat text format rather than JSON. It is
/// read inside a Roslyn analyzer, where a dependency that fails to load is not an
/// exception but a silently missing feature, and it is read by a person the day the
/// mapping looks wrong. Both of those are better served by a file you can `cut -f`.
/// </para>
/// </summary>
public sealed record VerificationDiagnostic(
    string Id,
    string File,
    int Line,
    int Column,
    int EndLine,
    int EndColumn,
    Severity Severity,
    string Message)
{
    /// <summary>Pulse could not discharge a proof obligation.</summary>
    public const string ErrorId = "PALCS0600";

    /// <summary>F* accepted the module but had something to say about it.</summary>
    public const string WarningId = "PALCS0601";

    /// <summary>The file <c>palcs report</c> writes and the analyzer reads.</summary>
    public const string FileName = "verification.txt";

    public static string Write(IEnumerable<VerificationDiagnostic> items)
    {
        var sb = new StringBuilder();
        sb.Append("# ").Append(FileName).Append(": what Pulse said, on the C# it was about.\n");
        sb.Append("# id\tfile\tline\tcol\tendLine\tendCol\tseverity\tmessage\n");
        foreach (var d in items)
        {
            sb.Append(d.Id).Append('\t')
              .Append(d.File).Append('\t')
              .Append(d.Line).Append('\t').Append(d.Column).Append('\t')
              .Append(d.EndLine).Append('\t').Append(d.EndColumn).Append('\t')
              .Append(d.Severity).Append('\t')
              .Append(Escape(d.Message)).Append('\n');
        }
        return sb.ToString();
    }

    public static ImmutableArray<VerificationDiagnostic> Read(string text)
    {
        var items = ImmutableArray.CreateBuilder<VerificationDiagnostic>();
        foreach (var line in text.Split('\n'))
        {
            if (line.Length == 0 || line[0] == '#') continue;
            var f = line.Split('\t');
            if (f.Length < 8) continue;
            if (!int.TryParse(f[2], out var l) || !int.TryParse(f[3], out var c) ||
                !int.TryParse(f[4], out var el) || !int.TryParse(f[5], out var ec)) continue;
            var severity = f[6] switch
            {
                "Error" => Severity.Error,
                "Warning" => Severity.Warning,
                _ => Severity.Info,
            };
            items.Add(new VerificationDiagnostic(f[0], f[1], l, c, el, ec, severity, Unescape(f[7])));
        }
        return items.ToImmutable();
    }

    private static string Escape(string s) =>
        s.Replace("\\", "\\\\").Replace("\t", "\\t").Replace("\r", "").Replace("\n", "\\n");

    private static string Unescape(string s)
    {
        var sb = new StringBuilder(s.Length);
        for (var i = 0; i < s.Length; i++)
        {
            if (s[i] != '\\' || i + 1 == s.Length) { sb.Append(s[i]); continue; }
            i++;
            sb.Append(s[i] switch { 'n' => '\n', 't' => '\t', var other => other });
        }
        return sb.ToString();
    }

    public override string ToString() =>
        $"{File}({Line},{Column}): {(Severity == Severity.Error ? "error" : "warning")} {Id}: {Message}";
}
