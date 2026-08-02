using System.Collections.Immutable;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using Pal.Compiler.Ir;

namespace Pal.Compiler.Frontend;

/// <summary>Attribute queries shared by the collector and the lowerers.</summary>
public static class Declarations
{
    public static bool Has(ISymbol symbol, INamedTypeSymbol attribute) =>
        symbol.GetAttributes().Any(a =>
            SymbolEqualityComparer.Default.Equals(a.AttributeClass, attribute));

    public static AttributeData? Find(ISymbol symbol, INamedTypeSymbol attribute) =>
        symbol.GetAttributes().FirstOrDefault(a =>
            SymbolEqualityComparer.Default.Equals(a.AttributeClass, attribute));

    public static ImmutableArray<AttributeData> All(ISymbol symbol, INamedTypeSymbol attribute) =>
        [.. symbol.GetAttributes().Where(a =>
            SymbolEqualityComparer.Default.Equals(a.AttributeClass, attribute))];

    /// <summary>The first string argument of an attribute application, if any.</summary>
    public static string? StringArgument(AttributeData data, int index = 0) =>
        data.ConstructorArguments.Length > index &&
        data.ConstructorArguments[index].Value is string s ? s : null;

    /// <summary>
    /// Which of the three kinds of translatable declaration a method is, or
    /// <c>null</c> if it is not translatable at all.
    /// </summary>
    public static CalleeKind? KindOf(IMethodSymbol method, WellKnown known)
    {
        if (Has(method, known.SpecAttribute)) return CalleeKind.Spec;
        if (Has(method, known.LemmaAttribute)) return CalleeKind.Lemma;
        if (method is { IsStatic: true, MethodKind: MethodKind.Ordinary }) return CalleeKind.Method;

        // §4.5. An instance method or constructor of a translated class: it carries the
        // object's invariant, which is what makes it translatable at all.
        return method is { IsStatic: false, MethodKind: MethodKind.Ordinary or MethodKind.Constructor }
               && method.ContainingType is { TypeKind: TypeKind.Class } owner
               && known.HasModel(owner)
            ? CalleeKind.Method
            : null;
    }

    /// <summary>
    /// R4.11. Whether a method leaves its receiver's model unchanged, decided from the
    /// body rather than from an annotation.
    /// </summary>
    /// <remarks>
    /// The test is deliberately syntactic and one level deep: a method is read-only when
    /// it assigns no field and calls no instance method. Anything deeper would need a
    /// fixpoint over the call graph, and getting it wrong in the permissive direction is
    /// unsound — a caller would be told the model did not move when it did. Getting it
    /// wrong in the strict direction only costs the caller an existential, which is
    /// exactly what it would have had without R4.11 at all.
    /// </remarks>
    public static bool IsReadOnly(IMethodSymbol method, Compilation compilation)
    {
        if (method.MethodKind == MethodKind.Constructor) return false;

        var syntax = method.DeclaringSyntaxReferences.FirstOrDefault()?.GetSyntax();
        if (syntax is null || !compilation.ContainsSyntaxTree(syntax.SyntaxTree)) return false;
        var model = compilation.GetSemanticModel(syntax.SyntaxTree);

        return !Mutates(syntax, model);
    }

    /// <summary>
    /// Whether a body moves an object's model. Three ways: assigning an instance field,
    /// writing through one — an element of an array the object owns is as much a part of
    /// its model as a scalar field is (R3.10a) — and calling an instance method or handing
    /// an owned array to a callee that might write it.
    /// </summary>
    public static bool Mutates(SyntaxNode syntax, SemanticModel model)
    {
        foreach (var node in syntax.DescendantNodes())
        {
            var target = node switch
            {
                AssignmentExpressionSyntax a => a.Left,
                PrefixUnaryExpressionSyntax p when p.IsKind(SyntaxKind.PreIncrementExpression)
                    || p.IsKind(SyntaxKind.PreDecrementExpression) => p.Operand,
                PostfixUnaryExpressionSyntax p when p.IsKind(SyntaxKind.PostIncrementExpression)
                    || p.IsKind(SyntaxKind.PostDecrementExpression) => p.Operand,
                _ => null,
            };
            // `items[i] = v` assigns no field symbol — the target is an element access —
            // but R3.10a says the array's contents *are* part of the model, so writing one
            // moves the model exactly as `n = n + 1` does. Peeling to the root is what
            // distinguishes it from a write into an unrelated local array.
            if (target is not null &&
                model.GetSymbolInfo(RootOf(target)).Symbol is IFieldSymbol { IsStatic: false })
                return true;

            if (node is InvocationExpressionSyntax call)
            {
                if (model.GetSymbolInfo(call).Symbol is IMethodSymbol
                        { IsStatic: false, MethodKind: MethodKind.Ordinary })
                    return true;

                // An owned array handed to a callee may come back written. Assuming it
                // does is the strict direction, and the strict direction costs a caller an
                // existential; the permissive one would be a lie.
                foreach (var argument in call.ArgumentList.Arguments)
                    if (model.GetSymbolInfo(RootOf(argument.Expression)).Symbol
                            is IFieldSymbol { IsStatic: false, Type: IArrayTypeSymbol })
                        return true;
            }
        }
        return false;
    }

    /// <summary>
    /// The expression an assignment or an argument ultimately reaches through: indexing and
    /// parentheses are peeled away, so that <c>this.items[i]</c> and <c>items[i]</c> both
    /// arrive at the field <c>items</c>.
    /// </summary>
    private static ExpressionSyntax RootOf(ExpressionSyntax expression) => expression switch
    {
        ElementAccessExpressionSyntax e => RootOf(e.Expression),
        ParenthesizedExpressionSyntax p => RootOf(p.Expression),
        _ => expression,
    };

    /// <summary>
    /// Whether the member carries any annotation that only means something to pal-csharp.
    /// </summary>
    /// <remarks>
    /// This is what separates "the user did not ask us to translate this" from "the user
    /// asked and we cannot yet oblige". Only the second is a diagnostic — but it must be
    /// one, because a silently dropped contract is a proof that was never attempted and
    /// looks exactly like a proof that succeeded.
    /// </remarks>
    public static bool IsAnnotated(ISymbol symbol, WellKnown known) =>
        symbol.GetAttributes().Any(a =>
            a.AttributeClass is { ContainingNamespace.Name: WellKnown.Namespace });

    /// <summary>
    /// The syntactic location an attribute's argument occupies, so that a diagnostic
    /// about a spec string lands on the string rather than on the declaration.
    /// </summary>
    public static Location ArgumentLocation(AttributeData data, int index = 0)
    {
        if (data.ApplicationSyntaxReference?.GetSyntax()
                is Microsoft.CodeAnalysis.CSharp.Syntax.AttributeSyntax syntax &&
            syntax.ArgumentList is { } list && list.Arguments.Count > index)
        {
            return SpecBinder.ContentLocation(list.Arguments[index].Expression);
        }
        return data.ApplicationSyntaxReference?.GetSyntax().GetLocation() ?? Location.None;
    }

    public static ParamMode ModeOf(IParameterSymbol p) => p.RefKind switch
    {
        RefKind.Ref => ParamMode.Ref,
        RefKind.Out => ParamMode.Out,
        RefKind.In or RefKind.RefReadOnlyParameter => ParamMode.In,
        _ => ParamMode.Value,
    };
}
