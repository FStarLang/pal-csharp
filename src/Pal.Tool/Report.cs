using System.Collections.Immutable;
using System.Text.Json;
using Pal.Compiler.Diagnostics;

namespace Pal.Tool;

/// <summary>
/// <c>palcs report -o OUT</c> — read F*'s JSON messages on stdin and say them in C#.
///
/// <para>
/// F* reports against the generated Pulse, which is the honest thing for it to do: it
/// checked that file and nothing else. But nobody wrote that file. The emitter is the only
/// thing that knows what each generated line was <em>for</em>, so it records that as it
/// goes (<c>line_map.json</c>), and this reads it back the other way.
/// </para>
/// <para>
/// The mapping is by containment, not by equality: an error on generated line <c>n</c>
/// belongs to the last construct that started at or before <c>n</c>. That is the right
/// rule because one C# statement becomes several Pulse ones and only the first of them is
/// recorded — the temporaries, the folds and the discards in between are the translation's
/// own, and attributing them to the statement that caused them is what a reader wants. A
/// line before any construct at all — a preamble, an <c>open</c> — falls back to the
/// declaration the module was generated from, which is still a true answer.
/// </para>
/// <para>
/// Nothing here interprets what F* said. The message is passed through verbatim, including
/// the Pulse names in it, because rewriting a prover's explanation into something friendlier
/// is how a tool starts lying about proofs. What changes is only *where* it is reported.
/// </para>
/// </summary>
public static class Report
{
    private sealed record Origin(int Line, string File, int StartLine, int StartCol, int EndLine, int EndCol);

    private sealed record Module(string File, ImmutableArray<Origin> Lines, Origin? Fallback);

    public static int Run(string output, bool quiet)
    {
        var mapPath = Path.Combine(output, "line_map.json");
        if (!File.Exists(mapPath))
        {
            Console.Error.WriteLine($"palcs report: no {mapPath}; run `palcs -o {output}` first");
            return 2;
        }

        var modules = LoadMap(mapPath);
        var found = ImmutableArray.CreateBuilder<VerificationDiagnostic>();
        var unmapped = 0;

        for (var line = Console.In.ReadLine(); line is not null; line = Console.In.ReadLine())
        {
            // F* writes its summary lines ("Verified module: M", "All verification
            // conditions discharged successfully", "1 error was reported") as prose even
            // under --message_format json. Anything that is not an object is therefore not
            // a message, and is passed through untouched: it is the build log's evidence
            // that the proof ran, and a filter that ate it would make a silent build
            // indistinguishable from a skipped one.
            var trimmed = line.Trim();
            if (trimmed.Length == 0 || trimmed[0] != '{') { Console.Out.WriteLine(line); continue; }

            JsonElement message;
            try { message = JsonDocument.Parse(trimmed).RootElement; }
            catch (JsonException) { Console.Out.WriteLine(line); continue; }

            if (IsCastDeprecation(message)) continue;

            if (Locate(message, modules) is not { } located)
            {
                // Not about anything this translation produced, or deliberately dropped
                // (see Locate). If it was nevertheless an error or a warning, say so where
                // F* said it: an error this filter could not place is still an error, and
                // swallowing it would leave a failing build with no explanation in it.
                if (Passthrough(message) is { } verbatim) Console.Error.WriteLine(verbatim);
                unmapped++;
                continue;
            }

            var (origin, severity) = located;
            found.Add(new VerificationDiagnostic(
                severity == Severity.Error
                    ? VerificationDiagnostic.ErrorId
                    : VerificationDiagnostic.WarningId,
                origin.File, origin.StartLine, origin.StartCol, origin.EndLine, origin.EndCol,
                severity, Text(message)));
        }

        var text = VerificationDiagnostic.Write(found);
        var path = Path.Combine(output, VerificationDiagnostic.FileName);
        if (!File.Exists(path) || File.ReadAllText(path) != text) File.WriteAllText(path, text);

        foreach (var d in found) Console.Error.WriteLine(d.ToString());

        if (!quiet)
            Console.Error.WriteLine(
                $"palcs report: {found.Count(d => d.Severity == Severity.Error)} error(s), " +
                $"{found.Count(d => d.Severity == Severity.Warning)} warning(s)" +
                (unmapped > 0 ? $", {unmapped} not mapped to any source" : ""));

        // The exit status is F*'s to give, not this filter's: it runs in a pipeline whose
        // job is to translate a message, and a translator that also passed judgement would
        // make a passing build depend on it having understood the output.
        return 0;
    }

    /// <summary>
    /// The C# an F* message is about, or nothing if it is about a file this translation
    /// did not produce (a library module, say — F* is entitled to complain about those and
    /// this has nothing useful to add).
    /// </summary>
    private static (Origin, Severity)? Locate(JsonElement message, ImmutableDictionary<string, Module> modules)
    {
        var severity = message.TryGetProperty("level", out var level) ? level.GetString() : "Error";
        if (severity is "Info" or "Feedback") return null;

        if (!message.TryGetProperty("range", out var range)) return null;

        // `def` is where F* raised the error; `use` is the term that provoked it. When they
        // differ, `use` is the narrower of the two -- `def` is the enclosing binding, which
        // for a Pulse `fn` can be the whole function -- so `use` is tried first and `def`
        // is the fallback. Either is skipped when it points outside this translation, which
        // is what happens when the error is raised against a library definition and used
        // here: then `use` is the generated module and `def` is the library, and the order
        // does not matter. It matters when both are in the generated module, and there the
        // narrower one is the one the user has to act on.
        //
        // The other order looked right until an array read went wrong: an index obligation
        // has `def` on the `bind` spanning the whole statement and `use` on the `read`, and
        // reporting `def` put "index may be out of bounds" on the method's signature line.
        // `test/pulse_refusals/cases/IndexInBounds.cs` is that program.
        foreach (var which in new[] { "use", "def" })
        {
            if (!range.TryGetProperty(which, out var r)) continue;
            if (!r.TryGetProperty("file_name", out var f) || f.GetString() is not { } file) continue;
            if (!modules.TryGetValue(Path.GetFileName(file), out var module)) continue;
            if (!r.TryGetProperty("start_pos", out var start) ||
                !start.TryGetProperty("line", out var lineNumber)) continue;

            var precise = Containing(module, lineNumber.GetInt32());

            // A warning that only maps to the module's fallback is almost never about the
            // program: F* warns about its own caches, its include path and its options,
            // all against a range in a file the user did not write. Claiming those are
            // about a particular class would be an invention. An *error* is reported
            // wherever it lands, because an error the user cannot see is worse than an
            // error in roughly the right place.
            var warning = severity == "Warning";
            var origin = warning ? precise : precise ?? module.Fallback;
            if (origin is null || (warning && origin == module.Fallback)) continue;

            return (origin, warning ? Severity.Warning : Severity.Error);
        }

        return null;
    }

    /// <summary>
    /// F*'s warning 288 on an <c>FStar.Int.Cast</c> conversion: those are deprecated because
    /// the result is implementation-defined in C, but R13.1 emits them on purpose for C#'s
    /// explicit casts, whose modular result C# defines. Dropped, not passed through.
    /// </summary>
    private static bool IsCastDeprecation(JsonElement message) =>
        message.TryGetProperty("number", out var n) && n.ValueKind == JsonValueKind.Number && n.GetInt32() == 288 &&
        message.TryGetProperty("msg", out var msg) && msg.ValueKind == JsonValueKind.Array && msg.GetArrayLength() > 0 &&
        msg[0].GetString() is { } first && first.StartsWith("FStar.Int.Cast.", StringComparison.Ordinal);

    /// <summary>
    /// An unmapped message, rendered at the location F* gave it. Purely informational
    /// output is dropped — F*'s own progress chatter is not a diagnostic — but anything
    /// that is an error or a warning survives, unplaced rather than unheard.
    /// </summary>
    private static string? Passthrough(JsonElement message)
    {
        var severity = message.TryGetProperty("level", out var level) ? level.GetString() : "Error";
        if (severity is "Info" or "Feedback") return null;

        var where = "";
        if (message.TryGetProperty("range", out var range) &&
            range.TryGetProperty("def", out var r) &&
            r.TryGetProperty("file_name", out var f) && f.GetString() is { } file)
        {
            var line = r.TryGetProperty("start_pos", out var start) &&
                       start.TryGetProperty("line", out var n) ? n.GetInt32() : 1;
            var col = start.TryGetProperty("col", out var c) ? c.GetInt32() : 0;
            where = $"{file}({line},{col}): ";
        }

        return $"{where}{(severity == "Warning" ? "warning" : "error")}: {Text(message)}";
    }

    private static Origin? Containing(Module module, int line)
    {
        Origin? best = null;
        foreach (var origin in module.Lines)
        {
            if (origin.Line > line) break;
            best = origin;
        }
        return best;
    }

    /// <summary>
    /// F*'s message is a list of paragraphs, each hard-wrapped for a terminal. The wraps
    /// are un-done and the paragraphs kept, so that the first line is the whole of "what
    /// could not be proved" — which is the only part some readers ever see, MSBuild and a
    /// squiggle's one-line summary among them — and the environment and the VC follow for
    /// anyone who opens the tooltip.
    /// </summary>
    private static string Text(JsonElement message)
    {
        if (!message.TryGetProperty("msg", out var msg) || msg.ValueKind != JsonValueKind.Array)
            return message.ToString();

        var paragraphs = msg.EnumerateArray()
            .Select(m => Unwrap(m.GetString() ?? ""))
            .Where(m => m.Length > 0);
        return string.Join("\n", paragraphs);

        static string Unwrap(string paragraph) =>
            string.Join(" ", paragraph.Split('\n').Select(l => l.Trim()).Where(l => l.Length > 0));
    }

    private static ImmutableDictionary<string, Module> LoadMap(string path)
    {
        var modules = ImmutableDictionary.CreateBuilder<string, Module>();
        foreach (var entry in JsonDocument.Parse(File.ReadAllText(path)).RootElement.EnumerateArray())
        {
            var file = entry.GetProperty("file").GetString()!;
            var lines = ImmutableArray.CreateBuilder<Origin>();
            foreach (var l in entry.GetProperty("lines").EnumerateArray())
                lines.Add(At(l.GetProperty("line").GetInt32(), l.GetProperty("source")));

            var fallback = entry.TryGetProperty("fallback", out var f) && f.ValueKind == JsonValueKind.Object
                ? At(0, f)
                : null;

            modules[file] = new Module(file, lines.ToImmutable(), fallback);
        }
        return modules.ToImmutable();

        // The map is written in LSP's zero-based convention; a diagnostic on a command
        // line is one-based, and so is Roslyn's.
        static Origin At(int line, JsonElement source)
        {
            var range = source.GetProperty("range");
            var start = range.GetProperty("start");
            var end = range.GetProperty("end");
            return new Origin(
                line,
                source.GetProperty("file").GetString()!,
                start.GetProperty("line").GetInt32() + 1,
                start.GetProperty("character").GetInt32() + 1,
                end.GetProperty("line").GetInt32() + 1,
                end.GetProperty("character").GetInt32() + 1);
        }
    }
}
