using System.Collections.Immutable;
using System.Diagnostics;
using System.Text;
using System.Text.Json;
using Microsoft.CodeAnalysis;
using Pal.Compiler.Diagnostics;
using Pal.Compiler.Emit;
using Pal.Compiler.Frontend;
using Pal.Compiler.Ir;
using Pal.Compiler.Passes;

namespace Pal.Tool;

/// <summary>
/// <c>palcs</c> — translate annotated C# to Pulse.
///
/// <para>
/// Usage: <c>palcs [-o OUT] [--print-ir] [--time-passes] [-q] &lt;files…&gt;</c>
/// </para>
/// <para>
/// <c>palcs report -o OUT</c> is the other direction: F*'s JSON messages on stdin, said
/// again against the C# they are about. See <see cref="Report"/>.
/// </para>
/// </summary>
public static class Program
{
    public static int Main(string[] args)
    {
        var sources = new List<string>();
        var output = ".";
        var report = args.Length > 0 && args[0] == "report";
        if (report) args = [.. args.Skip(1)];
        var printIr = false;
        var timePasses = false;
        var quiet = false;
        var nullable = true;

        for (var i = 0; i < args.Length; i++)
        {
            switch (args[i])
            {
                case "-o" or "--output" when i + 1 < args.Length: output = args[++i]; break;
                case "--print-ir": printIr = true; break;
                case "--time-passes": timePasses = true; break;
                case "-q" or "--quiet": quiet = true; break;
                // R20.9. A program written before nullable reference types is compiled
                // as it is built, so that its `string`s are the nullable ones it means.
                case "--nullable" when i + 1 < args.Length:
                    var mode = args[++i];
                    if (mode is not ("enable" or "disable"))
                    {
                        Console.Error.WriteLine($"palcs: --nullable takes `enable` or `disable`, not `{mode}`");
                        return 2;
                    }
                    nullable = mode == "enable";
                    break;
                case "-h" or "--help": Usage(); return 0;
                default:
                    if (args[i].StartsWith('-')) { Console.Error.WriteLine($"palcs: unknown option `{args[i]}`"); return 2; }
                    sources.Add(args[i]);
                    break;
            }
        }

        if (report) return Report.Run(output, quiet);

        if (sources.Count == 0) { Usage(); return 2; }

        var diagnostics = new DiagnosticBag();
        var watch = Stopwatch.StartNew();

        var compilation = Loader.Create(sources, nullable: nullable);
        var csharpErrors = compilation.GetDiagnostics()
            .Where(d => d.Severity == DiagnosticSeverity.Error)
            .ToList();
        if (csharpErrors.Count > 0)
        {
            // Translating a program the C# compiler rejects would report the same
            // mistakes a second time, in worse terms.
            foreach (var d in csharpErrors) Console.Error.WriteLine(d.ToString());
            return 1;
        }
        Stage("load", watch, timePasses);

        var program = FrontendPass.Run(compilation, diagnostics);
        Stage("frontend", watch, timePasses);

        program = Normalize.Run(program, diagnostics);
        Stage("normalize", watch, timePasses);

        program = Check.Run(program, diagnostics);
        Stage("check", watch, timePasses);

        if (printIr) Console.WriteLine(Printer.Print(program));

        var modules = new PulseEmitter(diagnostics).Emit(program);
        Stage("emit", watch, timePasses);

        Directory.CreateDirectory(output);
        var written = 0;
        var current = new HashSet<string>(StringComparer.Ordinal);
        foreach (var module in modules)
        {
            if (module.Interface is { } iface)
            {
                current.Add(module.InterfaceFileName);
                if (WriteIfChanged(Path.Combine(output, module.InterfaceFileName), iface)) written++;
            }
            current.Add(module.FileName);
            if (WriteIfChanged(Path.Combine(output, module.FileName), module.Text)) written++;
        }
        current.Add("TranslationErrors.fst");
        written += Prune(output, current);

        // R2.4a. A verification result describes the translation it was produced from, and
        // does not outlive it. `verification.txt` is what `palcs report` writes and the
        // analyzer reads back, so that a failed proof is shown on the C# that caused it;
        // left in place it shows a failure from a translation, or a translator, that no
        // longer exists -- which is how a phantom error survives the fix for it.
        //
        // The deletion is unconditional, and that costs nothing because F* writes a
        // `.checked` file only when a module *verifies*. A module that failed therefore
        // has none, the harness re-verifies exactly those, and a real failure is restated
        // on the next `make verify`. Deleting only on change would be the narrower rule
        // and the wrong one: it repairs the transition and not the state, so any file left
        // by an interrupted run, a crash or an older build stays forever.
        File.Delete(Path.Combine(output, VerificationDiagnostic.FileName));

        // PAL's sentinel: a module that fails to verify whenever translation was
        // incomplete, so a broken translation can never look like a passing proof.
        WriteIfChanged(Path.Combine(output, "TranslationErrors.fst"), TranslationErrors(diagnostics));
        WriteIfChanged(Path.Combine(output, "diagnostics.json"), diagnostics.ToJson());
        WriteIfChanged(Path.Combine(output, "source_range_info.json"), Provenance(modules));
        WriteIfChanged(Path.Combine(output, "line_map.json"), LineMap(modules));

        if (diagnostics.Items.Length > 0) Console.Error.Write(diagnostics.Render());
        if (!quiet)
            Console.Error.WriteLine(
                $"palcs: {modules.Length} module(s), {written} written, " +
                $"{diagnostics.Items.Count(d => d.Severity == Severity.Error)} error(s)");

        return diagnostics.HasErrors ? 1 : 0;
    }

    private static void Stage(string name, Stopwatch watch, bool report)
    {
        if (report) Console.Error.WriteLine($"palcs: {name} {watch.ElapsedMilliseconds} ms");
        watch.Restart();
    }

    /// <summary>
    /// R2.4. A module the last run wrote and this one did not is deleted, so a renamed or
    /// no-longer-emitted declaration cannot leave behind a module that is verified forever
    /// against C# that no longer exists. Only R2.1's own extensions are touched; the cache
    /// and the maps are left alone.
    /// </summary>
    private static int Prune(string output, HashSet<string> current)
    {
        var removed = 0;
        foreach (var pattern in new[] { "*.fst", "*.fsti" })
            foreach (var path in Directory.EnumerateFiles(output, pattern).ToArray())
                if (!current.Contains(Path.GetFileName(path)))
                {
                    File.Delete(path);
                    removed++;
                }
        return removed;
    }

    /// <summary>
    /// Writing only on change keeps F*'s checked-file cache warm across runs.
    /// </summary>
    private static bool WriteIfChanged(string path, string text)
    {
        if (File.Exists(path) && File.ReadAllText(path) == text) return false;
        File.WriteAllText(path, text);
        return true;
    }

    /// <summary>
    /// R2.2. Where each generated construct came from. The provenance lint reads this and
    /// reports anything the emitter produced that no C# asked for.
    /// </summary>
    private static string Provenance(ImmutableArray<EmittedModule> modules) =>
        JsonSerializer.Serialize(
            modules.SelectMany(m => m.Origin.Select(o => new
            {
                module = m.Name,
                file = m.FileName,
                construct = o.Construct,
                source = new
                {
                    file = o.Loc.File,
                    range = new
                    {
                        start = new { line = o.Loc.Line - 1, character = o.Loc.Column - 1 },
                        end = new { line = o.Loc.EndLine - 1, character = o.Loc.EndColumn - 1 },
                    },
                },
            })),
            new JsonSerializerOptions { WriteIndented = true });

    /// <summary>
    /// Which C# each *line* of each generated module came from, so that an F* error —
    /// which arrives as a range in a `.fst` nobody wrote — can be reported against the
    /// source. `source_range_info.json` answers a different question, "what does this
    /// module declare and why", which the provenance lint reads; keeping them apart keeps
    /// each one readable.
    ///
    /// A module also carries a fallback: an error on a line with no origin of its own —
    /// a preamble, an `open`, a brace — is still an error about that declaration, and
    /// saying so is better than saying nothing.
    /// </summary>
    private static string LineMap(ImmutableArray<EmittedModule> modules) =>
        JsonSerializer.Serialize(
            modules.Where(m => !m.Origins.IsDefaultOrEmpty || !m.Origin.IsDefaultOrEmpty)
                .Select(m => new
                {
                    file = m.FileName,
                    fallback = m.Origin.IsDefaultOrEmpty ? null : Range(m.Origin[0].Loc),
                    lines = m.Origins.Select(o => new { line = o.Line, source = Range(o.Source) }),
                }),
            new JsonSerializerOptions { WriteIndented = true });

    private static object Range(IrLoc loc) => new
    {
        file = loc.File,
        range = new
        {
            start = new { line = loc.Line - 1, character = loc.Column - 1 },
            end = new { line = loc.EndLine - 1, character = loc.EndColumn - 1 },
        },
    };

    private static string TranslationErrors(DiagnosticBag diagnostics)
    {
        var sb = new StringBuilder();
        sb.AppendLine("module TranslationErrors");
        sb.AppendLine();
        foreach (var d in diagnostics.Items.Where(x => x.Severity == Severity.Error))
            sb.AppendLine($"/// {d}");
        sb.AppendLine();
        sb.AppendLine(diagnostics.HasErrors
            ? "let translation_failed : unit = assert False"
            : "let translation_succeeded : unit = ()");
        return sb.ToString();
    }

    private static void Usage() => Console.Error.WriteLine(
        """
        palcs — translate annotated C# to Pulse

          palcs [options] <file.cs>...
          palcs report -o DIR          < fstar --message_format json output

        The second form maps F*'s messages about the generated Pulse back onto the C# they
        came from, writing `DIR/verification.txt` for an editor and printing them for a
        person. Verification is Pulse's job; this only says where.

        Options:
          -o, --output DIR   where to write the generated modules (default: .)
              --print-ir     dump the IR after normalisation
              --time-passes  report per-stage timings
          -q, --quiet        suppress the summary line
              --nullable M   compile with nullable reference types `enable`d (default) or `disable`d
          -h, --help         show this message
        """);
}
