using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;

namespace Pal.Compiler.Frontend;

/// <summary>
/// R30.29. A <c>ref</c>-returning method whose body binds or returns
/// <c>Unsafe.NullRef&lt;T&gt;()</c> — a lookup returning a reference to what it found, or a
/// null reference — is translated as returning an <c>option</c>: <c>None</c> for the null
/// reference, <c>Some v</c> for a reference to <c>v</c>. The reference is read once, where it
/// is bound; it is the same as reading it at each use when nothing can write what it points
/// to in between: the method must be read-only (it writes no field of its object, and calls
/// nothing that may), and so must the stretch of a caller in which it holds the reference.
/// </summary>
public static class RefSnapshots
{
    public static bool IsSnapshot(IMethodSymbol? method, Compilation compilation)
    {
        if (method is not { ReturnsByRef: true } && method is not { ReturnsByRefReadonly: true }) return false;
        if (method.OriginalDefinition.DeclaringSyntaxReferences is not [var reference] ||
            reference.GetSyntax() is not MethodDeclarationSyntax { Body: { } body })
            return false;
        // A contract is bound in a compilation of its own, without the body's tree; there the
        // call is recognised by its spelling.
        if (!compilation.ContainsSyntaxTree(body.SyntaxTree))
            return body.DescendantNodes().OfType<InvocationExpressionSyntax>().Any(c =>
                c is { ArgumentList.Arguments.Count: 0, Expression: MemberAccessExpressionSyntax
                {
                    Expression: IdentifierNameSyntax { Identifier.ValueText: "Unsafe" },
                    Name.Identifier.ValueText: "NullRef",
                } });
        var model = compilation.GetSemanticModel(body.SyntaxTree);
        return body.DescendantNodes().OfType<InvocationExpressionSyntax>().Any(c => IsNullRef(c, model));
    }

    private static bool IsUnsafe(IMethodSymbol m, string name) =>
        m.Name == name && m.ContainingType?.ToDisplayString() == "System.Runtime.CompilerServices.Unsafe";

    /// <summary><c>Unsafe.NullRef&lt;T&gt;()</c>.</summary>
    public static bool IsNullRef(ExpressionSyntax e, SemanticModel model)
    {
        while (e is ParenthesizedExpressionSyntax p) e = p.Expression;
        return e is InvocationExpressionSyntax { ArgumentList.Arguments.Count: 0 } call &&
               model.GetSymbolInfo(call).Symbol is IMethodSymbol m && IsUnsafe(m, "NullRef");
    }

    /// <summary><c>Unsafe.IsNullRef(ref x)</c>.</summary>
    public static bool IsIsNullRef(IMethodSymbol m) => IsUnsafe(m, "IsNullRef");

    /// <summary>The method a statement or expression is in, if it is a snapshot method.</summary>
    public static IMethodSymbol? Enclosing(SyntaxNode node, SemanticModel model) =>
        model.GetEnclosingSymbol(node.SpanStart) is IMethodSymbol { MethodKind: not (MethodKind.LambdaMethod or MethodKind.LocalFunction) } m &&
        IsSnapshot(m, model.Compilation) ? m : null;
}
