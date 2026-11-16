using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using Pal.Compiler.Diagnostics;
using Pal.Compiler.Ir;

namespace Pal.Compiler.Frontend;

internal static class Async
{
    // Forwarding transfers the completion promise, without exposing task identity.
    // Checking the forwarded completion against this method's contract is the same
    // obligation as checking an awaited return.
    internal static IrStmt? ForwardedBody(IrStmt? body) => body switch
    {
        IrReturn { Value: { Type: IrTaskType t } value } r =>
            r with { Value = new IrAsync(value.Loc, AsyncOp.Await, value) { Type = t.Result } },
        IrBlock b => b with { Statements = [.. b.Statements.Select(s => ForwardedBody(s)!)] },
        IrIf i => i with { Then = ForwardedBody(i.Then)!, Else = ForwardedBody(i.Else) },
        _ => body,
    };
    internal static bool IsTask(ITypeSymbol? type) =>
        type is INamedTypeSymbol t &&
        t.OriginalDefinition.ToDisplayString() is "System.Threading.Tasks.Task" or "System.Threading.Tasks.Task<TResult>";

    internal static ITypeSymbol Result(ITypeSymbol type, Compilation compilation) =>
        type is INamedTypeSymbol { TypeArguments: [var result] } && IsTask(type) ? result :
        IsTask(type) ? compilation.GetSpecialType(SpecialType.System_Void) : type;

    internal static bool Admissible(IMethodSymbol method, SyntaxNode syntax, WellKnown known,
        DiagnosticBag diagnostics, IrLoc loc)
    {
        var task = IsTask(method.ReturnType);
        var nodes = syntax.DescendantNodes().ToList();
        var hasTasks = task || nodes.OfType<AwaitExpressionSyntax>().Any();
        if (!hasTasks && !method.IsAsync) return true;
        string? reason =
            method.IsAsync && !task ? "Only async Task and async Task<T> are supported, not async void or custom awaitables."
            : method.IsVirtual || method.IsOverride || method.IsAbstract ? "Async virtual dispatch is not supported."
            : !method.IsStatic && known.HasModel(method.ContainingType) ? "Async methods on modelled receivers are not supported yet."
            : method.Parameters.Any(p => p.RefKind != RefKind.None ||
                known.MapType(p.Type) is IrClassType or IrSpanType or IrTaskType) ?
                "Async parameters must be values, arrays, or explicitly modelled SpecTypes; ref/span/object/task parameters are not supported yet."
            : Declarations.Has(method, known.ThrowsAttribute) ||
              nodes.Any(n => n is TryStatementSyntax or ThrowStatementSyntax or ThrowExpressionSyntax or LockStatementSyntax) ?
                "Async exception recovery and thread-affine locks are not supported. Contracts describe normal completion only."
            : null;
        if (reason is null) return true;
        diagnostics.Unsupported(loc, reason);
        return false;
    }
}
