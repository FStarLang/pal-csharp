using System;
using System.Collections.Immutable;
using System.Linq;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.Diagnostics;
using Microsoft.CodeAnalysis.Text;
using Pal.Compiler.Diagnostics;
using Pal.Compiler.Emit;
using Pal.Compiler.Frontend;
using Pal.Compiler.Ir;
using Pal.Compiler.Passes;

namespace Pal.Analyzers;

/// <summary>
/// pal-csharp's diagnostics, in the editor.
///
/// The analyzer states no rule of its own. It runs the compiler's own passes over the
/// compilation the IDE already has, and turns each <c>PalDiagnostic</c> into a Roslyn one.
/// Everything that <c>palcs</c> refuses, the editor underlines, in the same words and at
/// the same span; everything <c>palcs</c> accepts, the editor leaves alone. There is no
/// second copy of the subset to drift out of step, which is the same reason a self-call
/// gets a Pulse error rather than a compiler refusal.
///
/// That parity is why the emitter runs too, and why its output is then thrown away. Eight
/// of the refusals — an unbridgeable type, a measure over an array, an unsupported
/// specification term — are only discovered while emitting, and an editor that reported
/// the other twenty-eight would be worse than one that reported none: it would tell a user
/// who had cleared every squiggle that the program was ready, and the build would then
/// disagree. Emission is string building over an IR that is already in hand, so the
/// parity costs little.
///
/// It stops short of writing anything and of running F*. Verification is a separate, slow,
/// deliberate act; what an editor can give for free is the answer to "is this program
/// inside the language at all", and that is what this gives.
/// </summary>
[DiagnosticAnalyzer(LanguageNames.CSharp)]
public sealed class PalAnalyzer : DiagnosticAnalyzer
{
    private const string Category = "pal-csharp";

    private static readonly ImmutableDictionary<string, DiagnosticDescriptor> Descriptors =
        Catalog.Ids.ToImmutableDictionary(
            entry => entry.Id,
            entry => new DiagnosticDescriptor(
                entry.Id,
                title: entry.Id,
                messageFormat: "{0}",
                category: Category,
                defaultSeverity: entry.Severity == Severity.Error
                    ? DiagnosticSeverity.Error
                    : entry.Severity == Severity.Warning
                        ? DiagnosticSeverity.Warning
                        : DiagnosticSeverity.Info,
                isEnabledByDefault: true));

    public override ImmutableArray<DiagnosticDescriptor> SupportedDiagnostics { get; } =
        [.. Descriptors.Values];

    /// <summary>
    /// The analysis is whole-program — a call needs its callee's contract, and a lemma
    /// needs its call site — so it cannot be done a file at a time. It is run once per
    /// compilation and then reported per file, which is the shape Roslyn expects for an
    /// expensive analysis and is what makes the squiggles live rather than build-only.
    /// The result is held in the compilation-start scope rather than in a field, because
    /// an analyzer instance outlives the compilation it is looking at.
    /// </summary>
    public override void Initialize(AnalysisContext context)
    {
        context.ConfigureGeneratedCodeAnalysis(GeneratedCodeAnalysisFlags.None);
        context.EnableConcurrentExecution();
        context.RegisterCompilationStartAction(start =>
        {
            var analysis = new Lazy<ImmutableArray<PalDiagnostic>>(
                () => Run(start.Compilation), isThreadSafe: true);
            start.RegisterSemanticModelAction(model => Report(model, analysis.Value));
        });
    }

    private static void Report(SemanticModelAnalysisContext context, ImmutableArray<PalDiagnostic> found)
    {
        var tree = context.SemanticModel.SyntaxTree;
        foreach (var d in found)
        {
            if (d.Location.File != tree.FilePath) continue;
            if (!Descriptors.TryGetValue(d.Id, out var descriptor)) continue;
            context.ReportDiagnostic(Diagnostic.Create(descriptor, Span(tree, d.Location), d.Message));
        }
    }

    private static ImmutableArray<PalDiagnostic> Run(Compilation compilation)
    {
        // A project that does not use the annotations is not a pal-csharp project, and
        // running the frontend over it would be work spent to report nothing.
        if (compilation is not CSharpCompilation cs ||
            cs.GetTypeByMetadataName("PalLang.RequiresAttribute") is null)
        {
            return [];
        }

        // The frontend reads a program the C# compiler has already accepted. Handing it
        // one that does not bind yet — which, in an editor, is most of the time — would
        // report the same mistakes a second time in worse terms, exactly as `palcs` avoids
        // doing.
        if (cs.GetDiagnostics().Any(d => d.Severity == DiagnosticSeverity.Error)) return [];

        var bag = new DiagnosticBag();
        try
        {
            var program = FrontendPass.Run(cs, bag);
            program = Normalize.Run(program, bag);
            program = Check.Run(program, bag);
            new PulseEmitter(bag).Emit(program);
        }
        catch (Exception)
        {
            // An analyzer that throws takes the editor's analysis down with it. A crash in
            // a pass is a bug in pal-csharp, and the place to see it is `palcs`.
            return bag.Items;
        }

        return bag.Items;
    }

    /// <summary>
    /// <c>IrLoc</c> is one-based line and column, and carries an end, including for a span
    /// *inside* a specification string. Roslyn wants an absolute character range, so the
    /// conversion goes through the file's line table.
    /// </summary>
    private static Location Span(SyntaxTree tree, IrLoc loc)
    {
        var text = tree.GetText();
        if (loc.Line <= 0 || loc.Line > text.Lines.Count) return Location.None;

        var start = Offset(text, loc.Line, loc.Column);
        var end = loc.EndLine > 0 ? Offset(text, loc.EndLine, loc.EndColumn) : start;
        return Location.Create(tree, TextSpan.FromBounds(start, Math.Max(start, end)));

        static int Offset(SourceText text, int line, int column)
        {
            var l = text.Lines[Math.Min(Math.Max(line, 1), text.Lines.Count) - 1];
            return Math.Min(l.Start + Math.Max(column - 1, 0), l.EndIncludingLineBreak);
        }
    }
}
