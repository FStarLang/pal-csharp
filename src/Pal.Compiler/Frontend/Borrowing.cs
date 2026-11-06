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
        if (type is not INamedTypeSymbol s) return null;
        // R29.3. A sealed class with no model of its own, deriving from nothing, borrows
        // as a struct does: its state is the record of its fields.
        if (!(s.TypeKind == TypeKind.Struct ||
              s is { TypeKind: TypeKind.Class, IsSealed: true, IsStatic: false, BaseType.SpecialType: SpecialType.System_Object } &&
              !known.HasModel(s.OriginalDefinition) && !Declarations.Has(s.OriginalDefinition, known.PlainAttribute)))
            return null;
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

    /// <summary>
    /// R29.3b. Whether <paramref name="a"/> fills a view cache: <c>f ??= new V(this)</c>,
    /// where <c>f</c> is an instance field typed at a borrowing class <c>V</c> whose owner is
    /// <c>f</c>'s own class, and every write to <c>f</c> anywhere is such a fill. Such a field
    /// is in no representation (R29.3), and what it holds is then always <c>null</c> or a
    /// view of the object it is a field of, which as a record is <c>new V(this)</c>.
    /// </summary>
    public static bool IsViewCacheFill(AssignmentExpressionSyntax a, SemanticModel model, WellKnown known)
    {
        if (!a.IsKind(SyntaxKind.CoalesceAssignmentExpression)) return false;
        if (model.GetSymbolInfo(a.Left).Symbol is not IFieldSymbol { IsStatic: false } f) return false;
        if (!IsFillOf(a, f, model, known)) return false;
        foreach (var r in f.ContainingType.OriginalDefinition.DeclaringSyntaxReferences)
        {
            if (!model.Compilation.ContainsSyntaxTree(r.SyntaxTree)) return false;
            var m = model.Compilation.GetSemanticModel(r.SyntaxTree);
            foreach (var node in r.GetSyntax().DescendantNodes())
            {
                var written = node switch
                {
                    AssignmentExpressionSyntax w => w.Left,
                    ArgumentSyntax { RefKindKeyword.RawKind: not 0 } arg => arg.Expression,
                    _ => null,
                };
                if (written is null) continue;
                if (!SymbolEqualityComparer.Default.Equals(m.GetSymbolInfo(written).Symbol?.OriginalDefinition, f.OriginalDefinition))
                    continue;
                if (node is not AssignmentExpressionSyntax w2 || !IsFillOf(w2, f, m, known)) return false;
            }
        }
        return true;
    }

    private static bool IsFillOf(AssignmentExpressionSyntax a, IFieldSymbol f, SemanticModel model, WellKnown known) =>
        a.IsKind(SyntaxKind.CoalesceAssignmentExpression) &&
        IsBorrowingClass(f.Type, known) &&
        SymbolEqualityComparer.Default.Equals(
            OwnerField(f.Type, known)!.Type.OriginalDefinition, f.ContainingType.OriginalDefinition) &&
        a.Right is BaseObjectCreationExpressionSyntax { ArgumentList.Arguments: [{ Expression: ThisExpressionSyntax, RefKindKeyword.RawKind: 0 }], Initializer: null } &&
        SymbolEqualityComparer.Default.Equals(
            model.GetTypeInfo(a.Right).Type?.OriginalDefinition, f.Type.OriginalDefinition);

    /// <summary>
    /// R27.37. The fields of a borrowing struct that own an object: <c>readonly</c>, typed at
    /// a class with a model that is not the borrowed one and holds no region.
    /// </summary>
    public static System.Collections.Immutable.ImmutableArray<IFieldSymbol> OwnedFields(ITypeSymbol? type, WellKnown known)
    {
        if (type is not INamedTypeSymbol { TypeKind: TypeKind.Struct } s || OwnerField(s, known) is not { } owner) return [];
        return [.. s.GetMembers().OfType<IFieldSymbol>().Where(f =>
            f is { IsStatic: false, IsConst: false, IsReadOnly: true } &&
            !SymbolEqualityComparer.Default.Equals(f, owner) &&
            f.Type is INamedTypeSymbol { TypeKind: TypeKind.Class } ft &&
            !known.IsRegionClass(ft) && known.HasModel(ft.OriginalDefinition))];
    }

    /// <summary>R27.37. The parameter an owned field's object arrives in.</summary>
    public static string OwnedName(IFieldSymbol f) => "__pal_own" + f.Name;
    public static string OwnedName(string field) => "__pal_own" + field;

    /// <summary>R29.3. Whether <paramref name="type"/> is a class that borrows (R28.1).</summary>
    public static bool IsBorrowingClass(ITypeSymbol? type, WellKnown known) =>
        type is { TypeKind: TypeKind.Class } && IsBorrowing(type, known);

    /// <summary>Whether <paramref name="type"/> is an R28.1 borrowing struct.</summary>
    public static bool IsBorrowing(ITypeSymbol? type, WellKnown known) => OwnerField(type, known) is not null;

    /// <summary>
    /// R28.2. Whether <paramref name="method"/> is a member of a borrowing struct that is
    /// translated: an instance method, accessor, constructor, or explicit interface
    /// implementation.
    /// </summary>
    public static bool IsMember(IMethodSymbol method, WellKnown known) =>
        method is { IsStatic: false,
                    MethodKind: MethodKind.Ordinary or MethodKind.Constructor or MethodKind.PropertyGet or MethodKind.PropertySet
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

    public static bool WritesState(SyntaxNode body, SemanticModel model, INamedTypeSymbol self) =>
        WritesState(body, model, self, new HashSet<SyntaxNode>());

    private static bool WritesState(SyntaxNode body, SemanticModel model, INamedTypeSymbol self, HashSet<SyntaxNode> seen)
    {
        if (!seen.Add(body)) return false;
        foreach (var node in body.DescendantNodes())
        {
            // R27.37. A call of a member of the same struct that writes it writes it too.
            if (node is InvocationExpressionSyntax { Expression: IdentifierNameSyntax or MemberAccessExpressionSyntax { Expression: ThisExpressionSyntax } } call &&
                model.GetSymbolInfo(call).Symbol is IMethodSymbol { IsStatic: false } callee &&
                SymbolEqualityComparer.Default.Equals(callee.ContainingType.OriginalDefinition, self.OriginalDefinition) &&
                callee.DeclaringSyntaxReferences.FirstOrDefault()?.GetSyntax() is { } decl &&
                model.Compilation.ContainsSyntaxTree(decl.SyntaxTree) &&
                WritesState(decl, model.Compilation.GetSemanticModel(decl.SyntaxTree), self, seen))
                return true;
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
    public static IParameterSymbol? OwnerParameter(IMethodSymbol ctor, IFieldSymbol owner, Compilation? compilation = null)
    {
        if (ctor.DeclaringSyntaxReferences.FirstOrDefault()?.GetSyntax() is not ConstructorDeclarationSyntax decl)
            return null;
        // R27.38. A constructor that only chains (`: this(set, false) { }`) passes the
        // borrowed object on: its parameter is the one given for the chained-to constructor's.
        if (decl.Initializer is { } init)
        {
            if (compilation is null || !init.ThisOrBaseKeyword.IsKind(SyntaxKind.ThisKeyword) ||
                decl.Body is { Statements.Count: > 0 } || decl.ExpressionBody is not null)
                return null;
            var m = compilation.GetSemanticModel(decl.SyntaxTree);
            if (m.GetSymbolInfo(init).Symbol is not IMethodSymbol target ||
                OwnerParameter(target, owner, compilation) is not { } tp)
                return null;
            foreach (var a in init.ArgumentList.Arguments)
                if (m.GetOperation(a) is Microsoft.CodeAnalysis.Operations.IArgumentOperation ao &&
                    SymbolEqualityComparer.Default.Equals(ao.Parameter, tp))
                    return a.Expression is IdentifierNameSyntax id
                        ? ctor.Parameters.FirstOrDefault(p => p.Name == id.Identifier.ValueText)
                        : null;
            return null;
        }
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
