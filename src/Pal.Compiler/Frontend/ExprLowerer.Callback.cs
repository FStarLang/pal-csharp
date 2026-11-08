using System.Collections.Immutable;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using Pal.Compiler.Diagnostics;
using Pal.Compiler.Emit;
using Pal.Compiler.Ir;

namespace Pal.Compiler.Frontend;

/// <summary>R27.39. Callbacks over region pointers, and the lambdas passed to them.</summary>
public sealed partial class ExprLowerer
{
    /// <summary>R27.39. The lambdas this lowerer lifted to methods, in the order it met them.</summary>
    public List<IrMethod> Lifted { get; init; } = [];

    /// <summary>R27.39. The name the lifted lambdas of a method are numbered under.</summary>
    public string? LiftPrefix { get; set; }

    /// <summary>R27.39. The type parameters the lifted lambdas are generic in: the enclosing method's.</summary>
    public ImmutableArray<string> LiftTypeParameters { get; set; } = [];

    /// <summary>R27.39. The variable naming the trace of the callback parameter <paramref name="action"/>.</summary>
    public static string TraceName(string action) => "__pal_trace_" + action;

    /// <summary>
    /// R27.39. What a <c>[Callback]</c> parameter is called with and returns, or null (with a
    /// diagnostic) when its delegate is not one taking a reference to a <c>[Region]</c> class
    /// and returning a value.
    /// </summary>
    public static IrCallback? CallbackOf(IParameterSymbol p, WellKnown known, DiagnosticBag diagnostics)
    {
        if (!Declarations.Has(p, known.CallbackAttribute)) return null;
        var loc = p.Locations.Length > 0 ? Locations.From(p.Locations[0]) : IrLoc.None;
        if (p.Type is INamedTypeSymbol { TypeKind: TypeKind.Delegate, DelegateInvokeMethod: { ReturnsVoid: false } invoke } &&
            invoke.Parameters is [{ RefKind: RefKind.None, Type: INamedTypeSymbol node }] &&
            known.IsRegionClass(node) && known.MapType(node) is IrClassType region &&
            node.GetMembers().FirstOrDefault(m => Declarations.Has(m, known.ModelAttribute)) is IPropertySymbol view &&
            known.MapType(view.Type) is { } viewType &&
            known.MapType(invoke.ReturnType) is { } result && p.RefKind == RefKind.None)
            return new IrCallback(region with { Nullable = false }, viewType, result);
        diagnostics.Error("PALCS0708", loc,
            $"The `[Callback]` parameter `{p.Name}` must be a delegate taking one reference to a " +
            "`[Region]` class and returning a value (doc/translation.md R27.39).");
        return null;
    }

    /// <summary>R27.39. The <c>[Callback]</c> parameter <paramref name="target"/> names, if it names one.</summary>
    private IrCallback? CallbackTarget(ExpressionSyntax target) =>
        model.GetSymbolInfo(target).Symbol is IParameterSymbol p && Declarations.Has(p, known.CallbackAttribute)
            ? CallbackOf(p, known, diagnostics)
            : null;

    /// <summary>
    /// R27.39. Whether <paramref name="target"/> may name a callback's trace: a contract is
    /// bound against a copy of the method whose parameters carry no attributes, so there a
    /// delegate parameter is accepted, and the scope says whether it has a trace.
    /// </summary>
    private bool TraceTarget(ExpressionSyntax target) =>
        model.GetSymbolInfo(target).Symbol is IParameterSymbol p &&
        (Declarations.Has(p, known.CallbackAttribute) || p.Type.TypeKind == TypeKind.Delegate);

    /// <summary>
    /// R27.39. <c>action(x)</c> on a <c>[Callback]</c> parameter: a call the emitter makes
    /// through the parameter, which extends its trace.
    /// </summary>
    private IrExpr? LowerCallbackInvoke(IMethodSymbol method, InvocationExpressionSyntax node, IrLoc loc)
    {
        if (method.MethodKind != MethodKind.DelegateInvoke) return null;
        var target = node.Expression is MemberAccessExpressionSyntax { Name.Identifier.ValueText: "Invoke" } inv
            ? inv.Expression : node.Expression;
        if (target is not IdentifierNameSyntax id || CallbackTarget(target) is not { } cb) return null;
        if (SpecPosition || node.ArgumentList.Arguments.Count != 1)
            return Refused("PALCS0708", loc,
                $"The `[Callback]` parameter `{id.Identifier.ValueText}` is called in code, with one argument " +
                "(doc/translation.md R27.39).");
        var name = id.Identifier.ValueText;
        return new IrCall(loc, name,
            [new IrVar(loc, TraceName(name)), NonNull(Lower(node.ArgumentList.Arguments[0].Expression))])
        {
            Kind = CalleeKind.Callback,
            ResultType = cb.Result,
            ParamTypes = [null, cb.Region],
        };
    }

    /// <summary>
    /// R27.39. <c>Pal.Trace&lt;TV, TR&gt;(action)</c>: the trace of the <c>[Callback]</c>
    /// parameter <c>action</c>, in a contract, an invariant or a ghost statement.
    /// </summary>
    private IrExpr LowerTrace(IMethodSymbol method, SeparatedSyntaxList<ArgumentSyntax> args, IrLoc loc)
    {
        if (args is not [{ Expression: IdentifierNameSyntax id }] || !TraceTarget(id))
            return Refused("PALCS0708", loc,
                "`Pal.Trace` takes a `[Callback]` parameter of the enclosing method (doc/translation.md R27.39).");
        return new IrVar(loc, TraceName(id.Identifier.ValueText)) { Type = known.MapType(method.ReturnType) };
    }

    /// <summary>
    /// R27.39. A lambda passed to a <c>[Callback]</c> parameter is lifted to a method of its
    /// own: it takes the trace, then the variables it captures (by reference those it writes),
    /// then the node; it requires its protocol on the trace and that the node is in the
    /// region, and ensures the protocol on the trace extended by this call.
    /// </summary>
    private IrExpr LowerCallbackArgument(ArgumentSyntax arg, IrCallback cb, IrLoc loc)
    {
        // R32.5. An anonymous method (`delegate (Node n) { … }`) is lifted as a lambda is.
        if (arg.Expression is not AnonymousFunctionExpressionSyntax lambda ||
            model.GetSymbolInfo(lambda).Symbol is not IMethodSymbol { Parameters: [var nodeParam] } lambdaSymbol)
            return Refused("PALCS0709", loc,
                "The argument to a `[Callback]` parameter is a lambda of one parameter " +
                "(doc/translation.md R27.39).");
        var statements = lambda.Block is { } blk ? blk.Statements.ToImmutableArray() : [];
        if (statements.IsEmpty ||
            statements[0] is not ExpressionStatementSyntax { Expression: InvocationExpressionSyntax protocolCall } ||
            model.GetSymbolInfo(protocolCall).Symbol is not IMethodSymbol { Name: nameof(PalLang.Pal.Protocol) } protocol ||
            !SymbolEqualityComparer.Default.Equals(protocol.ContainingType, known.Pal) ||
            protocolCall.ArgumentList.Arguments is not [{ Expression: LambdaExpressionSyntax inv }] ||
            inv.ExpressionBody is null ||
            model.GetSymbolInfo(inv).Symbol is not IMethodSymbol { Parameters: [var traceParam] })
            return Refused("PALCS0709", loc,
                "A lambda passed to a `[Callback]` parameter has a block body whose first statement is " +
                "`Pal.Protocol(tr => …)`, the invariant it keeps over the trace of its calls " +
                "(doc/translation.md R27.39).");

        var flow = model.AnalyzeDataFlow(lambda);
        if (flow is not { Succeeded: true })
            return Refused("PALCS0709", loc, "The lambda's captured variables could not be determined.");
        var captured = flow.CapturedInside
            .Where(s => s is ILocalSymbol or IParameterSymbol &&
                        !SymbolEqualityComparer.Default.Equals(s.ContainingSymbol, lambdaSymbol) &&
                        !SymbolEqualityComparer.Default.Equals(s, traceParam) &&
                        !SymbolEqualityComparer.Default.Equals(s.ContainingSymbol, model.GetSymbolInfo(inv).Symbol))
            .Distinct(SymbolEqualityComparer.Default)
            .OrderBy(s => s.Locations.FirstOrDefault()?.SourceSpan.Start ?? 0)
            .ToList();
        if (captured.Any(s => s is IParameterSymbol { IsThis: true }) ||
            flow.CapturedInside.Any(s => s is IParameterSymbol { IsThis: true }))
            return Refused("PALCS0709", loc,
                "A lambda passed to a `[Callback]` parameter that captures `this` " +
                "(doc/translation.md R27.39): the callee holds the object's region already.");
        var written = flow.WrittenInside.ToImmutableHashSet<ISymbol>(SymbolEqualityComparer.Default);

        var parameters = ImmutableArray.CreateBuilder<IrParam>();
        var traceType = known.MapType(traceParam.Type);
        if (traceType is null) return Refused("PALCS0709", loc, "The trace type of the protocol is not supported.");
        var trace = traceParam.Name;
        parameters.Add(new IrParam(loc, trace, traceType, ParamMode.Value) { IsGhost = true, ExplicitGhost = true });

        var captures = ImmutableArray.CreateBuilder<IrExpr>();
        foreach (var s in captured)
        {
            var type = s switch { ILocalSymbol l => l.Type, IParameterSymbol p => p.Type, _ => null };
            var ghost = known.IsGhost(type);
            if (type is null) return Refused("PALCS0709", loc, $"The captured variable `{s.Name}` has no type.");
            var mapped = known.MapType(ghost ? ((INamedTypeSymbol)type).TypeArguments[0] : type);
            if (mapped is null)
                return Refused("PALCS0709", loc, $"The captured variable `{s.Name}` has an unsupported type.");
            if (ghost && mapped is IrPrim { IsMachineInt: true }) mapped = IrPrim.SpecIntType;
            var byRef = !ghost && written.Contains(s) && mapped is not IrArrayType;
            if (ghost && written.Contains(s))
                return Refused("PALCS0709", loc, $"The lambda writes the captured ghost `{s.Name}`.");
            parameters.Add(new IrParam(loc, s.Name, mapped, byRef ? ParamMode.Ref : ParamMode.Value)
            {
                IsGhost = ghost, ExplicitGhost = ghost,
            });
            var v = new IrVar(loc, s.Name) { Type = mapped };
            captures.Add(byRef ? new IrRefArg(loc, v) : v);
        }
        var node = nodeParam.Name;
        parameters.Add(new IrParam(loc, node, cb.Region, ParamMode.Value) { Plain = true });

        var spec = new ExprLowerer(model, known, diagnostics, specPosition: true);
        var pre = spec.Lower(inv.ExpressionBody!);
        var heap = new IrVar(loc, Region.HeapName(cb.Region.Name)) { Type = IrPrim.SpecIntType };
        var nodeVar = new IrVar(loc, node) { Type = cb.Region };
        var viewAt = new IrSpecOp(loc,
            $"Pulse.Lib.CSharp.Callback.view_at {Emit.Names.ClassModule(cb.Region.Name)}.{Region.ViewOf(cb.Region.Name)}",
            [heap, nodeVar]) { Type = cb.View, MachineArgs = true };
        var entry = new IrSpecOp(loc, "Mktuple2", [viewAt, new IrResult(loc) { Type = cb.Result }])
            { MachineArgs = true };
        var extended = new IrSpecOp(loc, "Seq.snoc", [new IrVar(loc, trace) { Type = traceType }, entry])
            { Type = traceType, MachineArgs = true };
        var postLowerer = new ExprLowerer(model, known, diagnostics, specPosition: true);
        postLowerer.Alias(traceParam, extended);
        var post = postLowerer.Lower(inv.ExpressionBody!);
        var inRegion = new IrSpecOp(loc, $"{Region.Module}.mem", [heap, nodeVar]) { Type = IrPrim.Bool, MachineArgs = true };
        var bounded = new IrSpecOp(loc, "Pulse.Lib.CSharp.Callback.callable",
            [new IrVar(loc, trace) { Type = traceType }]) { Type = IrPrim.Bool, MachineArgs = true };

        var name = $"{LiftPrefix}_Lambda{Lifted.Count}";
        var body = new StmtLowerer(model, known, diagnostics);
        body.Expressions.LiftPrefix = name;
        body.Expressions.LiftTypeParameters = LiftTypeParameters;
        var lowered = statements.Skip(1).Select(body.Lower).ToImmutableArray();
        var method = new IrMethod(loc, name, parameters.ToImmutable(), cb.Result,
            [pre, bounded, inRegion], [post], null, new IrBlock(loc, lowered))
        {
            Lambda = new IrLambdaInfo(trace, node, cb),
            TypeParameters = LiftTypeParameters,
        };
        Lifted.Add(method);
        Lifted.AddRange(body.Expressions.Lifted);
        return new IrLambdaRef(loc, name, captures.ToImmutable())
        {
            Callback = cb,
            TypeArguments = [.. LiftTypeParameters.Select(t => (IrType)new IrTypeParamType(t))],
        };
    }
}
