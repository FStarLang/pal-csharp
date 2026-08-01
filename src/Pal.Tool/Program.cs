using System.Diagnostics;
using System.Text;
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
/// </summary>
public static class Program
{
    public static int Main(string[] args)
    {
        var sources = new List<string>();
        var output = ".";
        var printIr = false;
        var timePasses = false;
        var quiet = false;

        for (var i = 0; i < args.Length; i++)
        {
            switch (args[i])
            {
                case "-o" or "--output" when i + 1 < args.Length: output = args[++i]; break;
                case "--print-ir": printIr = true; break;
                case "--time-passes": timePasses = true; break;
                case "-q" or "--quiet": quiet = true; break;
                case "-h" or "--help": Usage(); return 0;
                default:
                    if (args[i].StartsWith('-')) { Console.Error.WriteLine($"palcs: unknown option `{args[i]}`"); return 2; }
                    sources.Add(args[i]);
                    break;
            }
        }

        if (sources.Count == 0) { Usage(); return 2; }

        var diagnostics = new DiagnosticBag();
        var watch = Stopwatch.StartNew();

        var compilation = Loader.Create(sources);
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
        foreach (var module in modules)
            if (WriteIfChanged(Path.Combine(output, module.FileName), module.Text)) written++;

        // PAL's sentinel: a module that fails to verify whenever translation was
        // incomplete, so a broken translation can never look like a passing proof.
        WriteIfChanged(Path.Combine(output, "TranslationErrors.fst"), TranslationErrors(diagnostics));
        WriteIfChanged(Path.Combine(output, "diagnostics.json"), diagnostics.ToJson());

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
    /// Writing only on change keeps F*'s checked-file cache warm across runs.
    /// </summary>
    private static bool WriteIfChanged(string path, string text)
    {
        if (File.Exists(path) && File.ReadAllText(path) == text) return false;
        File.WriteAllText(path, text);
        return true;
    }

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

        Options:
          -o, --output DIR   where to write the generated modules (default: .)
              --print-ir     dump the IR after normalisation
              --time-passes  report per-stage timings
          -q, --quiet        suppress the summary line
          -h, --help         show this message
        """);
}
