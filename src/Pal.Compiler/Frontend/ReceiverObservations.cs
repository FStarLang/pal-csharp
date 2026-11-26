using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp.Syntax;

namespace Pal.Compiler.Frontend;

/// <summary>
/// A pure receiver-identity observation is not a function of the object's model.
/// Inline this narrow form at reference-bearing call sites instead of inventing
/// a model-to-pointer function. All other observations keep the model-only ABI.
/// </summary>
internal static class ReceiverObservations
{
    public static bool IsIdentity(ISymbol symbol, WellKnown known)
    {
        if (symbol is not IPropertySymbol { IsStatic: false } p ||
            !Declarations.Has(p, known.SpecAttribute) ||
            !SymbolEqualityComparer.Default.Equals(p.Type, p.ContainingType))
            return false;
        foreach (var reference in p.DeclaringSyntaxReferences)
        {
            if (reference.GetSyntax() is not PropertyDeclarationSyntax property) continue;
            ExpressionSyntax? expression = property.ExpressionBody?.Expression;
            if (expression is null && property.AccessorList?.Accessors is { Count: 1 } accessors)
                expression = accessors[0].ExpressionBody?.Expression ??
                    (accessors[0].Body?.Statements is [ReturnStatementSyntax ret] ? ret.Expression : null);
            while (expression is ParenthesizedExpressionSyntax parens) expression = parens.Expression;
            if (expression is ThisExpressionSyntax) return true;
        }
        return false;
    }
}
