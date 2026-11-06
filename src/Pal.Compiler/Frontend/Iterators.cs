using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp.Syntax;

namespace Pal.Compiler.Frontend;

/// <summary>
/// R27.42. Iterator methods: a method returning <c>IEnumerable&lt;T&gt;</c> or
/// <c>IEnumerator&lt;T&gt;</c> whose body has <c>yield</c> statements. It is translated as
/// one whole enumeration, run to its end, returning the values it yielded in order.
/// </summary>
public static class Iterators
{
    /// <summary>The name of the local the translation accumulates the yielded values in.</summary>
    public const string Trace = "__pal_yielded";

    /// <summary>The element type of an iterator method; <c>null</c> for any other method.</summary>
    public static ITypeSymbol? Element(IMethodSymbol method)
    {
        if (method.ReturnType is not INamedTypeSymbol { IsGenericType: true, TypeArguments: [var element] } r ||
            r.OriginalDefinition.ToDisplayString() is not
                ("System.Collections.Generic.IEnumerable<T>" or "System.Collections.Generic.IEnumerator<T>"))
            return null;
        var body = method.DeclaringSyntaxReferences.FirstOrDefault()?.GetSyntax() switch
        {
            BaseMethodDeclarationSyntax m => (SyntaxNode?)m.Body ?? m.ExpressionBody,
            AccessorDeclarationSyntax a => (SyntaxNode?)a.Body ?? a.ExpressionBody,
            _ => null,
        };
        return body is not null && Yields(body) ? element : null;
    }

    private static bool Yields(SyntaxNode body) =>
        body.DescendantNodes(n => n is not (AnonymousFunctionExpressionSyntax or LocalFunctionStatementSyntax))
            .OfType<YieldStatementSyntax>().Any();
}
