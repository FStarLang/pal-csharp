using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;

namespace Pal.Compiler.Frontend;

/// <summary>
/// §28. A struct that *borrows* an object of an enclosing class: an enumerator. Its one
/// readonly field typed at an enclosing class with a model (R28.1) is a reference the
/// struct does not own, and its members are translated as members of that class (R28.2).
/// </summary>
public static class Borrowing
{
    /// <summary>
    /// R28.1. The borrowed field of <paramref name="type"/>: the single instance field that
    /// is <c>readonly</c> and typed at a class with a model enclosing the struct.
    /// </summary>
    public static IFieldSymbol? OwnerField(ITypeSymbol? type, WellKnown known)
    {
        if (type is not INamedTypeSymbol { TypeKind: TypeKind.Struct } s) return null;
        IFieldSymbol? found = null;
        foreach (var f in s.GetMembers().OfType<IFieldSymbol>())
        {
            if (f.IsStatic || f.IsConst || !f.IsReadOnly) continue;
            if (f.Type is not INamedTypeSymbol { TypeKind: TypeKind.Class } ft) continue;
            if (!Encloses(ft, s) || !known.HasModel(ft.OriginalDefinition)) continue;
            if (found is not null) return null;
            found = f;
        }
        return found;
    }

    /// <summary>Whether <paramref name="type"/> is an R28.1 borrowing struct.</summary>
    public static bool IsBorrowing(ITypeSymbol? type, WellKnown known) => OwnerField(type, known) is not null;

    /// <summary>
    /// R28.2. Whether <paramref name="method"/> is a member of a borrowing struct that is
    /// translated: an instance method, accessor, constructor, or explicit interface
    /// implementation.
    /// </summary>
    public static bool IsMember(IMethodSymbol method, WellKnown known) =>
        method is { IsStatic: false,
                    MethodKind: MethodKind.Ordinary or MethodKind.Constructor or MethodKind.PropertyGet
                                or MethodKind.ExplicitInterfaceImplementation }
        && IsBorrowing(method.ContainingType, known);

    private static bool Encloses(INamedTypeSymbol outer, INamedTypeSymbol inner)
    {
        for (var c = inner.ContainingType; c is not null; c = c.ContainingType)
            if (SymbolEqualityComparer.Default.Equals(c.OriginalDefinition, outer.OriginalDefinition))
                return true;
        return false;
    }

    /// <summary>
    /// R28.4. Whether a member writes the struct's own state. A struct member's receiver is
    /// a <c>ref</c> exactly when it does; a reader takes the struct by value.
    /// </summary>
    /// <summary>`++x`, `x--` and the like; not `!x` or `x!`.</summary>
    public static bool IsStep(SyntaxNode n) =>
        n.IsKind(SyntaxKind.PreIncrementExpression) || n.IsKind(SyntaxKind.PreDecrementExpression) ||
        n.IsKind(SyntaxKind.PostIncrementExpression) || n.IsKind(SyntaxKind.PostDecrementExpression);

    public static bool WritesState(SyntaxNode body, SemanticModel model, INamedTypeSymbol self)
    {
        foreach (var node in body.DescendantNodes())
        {
            var target = node switch
            {
                AssignmentExpressionSyntax a => a.Left,
                PrefixUnaryExpressionSyntax p when IsStep(p) => p.Operand,
                PostfixUnaryExpressionSyntax p when IsStep(p) => p.Operand,
                _ => null,
            };
            if (target is null) continue;
            while (target is ParenthesizedExpressionSyntax pe) target = pe.Expression;
            if (target is MemberAccessExpressionSyntax { Expression: ThisExpressionSyntax } or IdentifierNameSyntax &&
                model.GetSymbolInfo(target).Symbol is IFieldSymbol { IsStatic: false } f &&
                SymbolEqualityComparer.Default.Equals(f.ContainingType.OriginalDefinition, self.OriginalDefinition))
                return true;
        }
        return false;
    }

    /// <summary>
    /// R28.4. The constructor parameter the borrowed object arrives in: the one the
    /// borrowing field is assigned from.
    /// </summary>
    public static IParameterSymbol? OwnerParameter(IMethodSymbol ctor, IFieldSymbol owner)
    {
        if (ctor.DeclaringSyntaxReferences.FirstOrDefault()?.GetSyntax() is not ConstructorDeclarationSyntax decl)
            return null;
        IEnumerable<ExpressionSyntax> exprs = decl.Body?.Statements.OfType<ExpressionStatementSyntax>()
            .Select(s => s.Expression) ?? [];
        if (decl.ExpressionBody is { } eb) exprs = [eb.Expression];
        foreach (var e in exprs)
        {
            if (e is not AssignmentExpressionSyntax { Left: var left, Right: IdentifierNameSyntax right }) continue;
            var name = left switch
            {
                IdentifierNameSyntax i => i.Identifier.ValueText,
                MemberAccessExpressionSyntax { Expression: ThisExpressionSyntax, Name: var n } => n.Identifier.ValueText,
                _ => null,
            };
            if (name != owner.Name) continue;
            return ctor.Parameters.FirstOrDefault(p => p.Name == right.Identifier.ValueText);
        }
        return null;
    }
}
