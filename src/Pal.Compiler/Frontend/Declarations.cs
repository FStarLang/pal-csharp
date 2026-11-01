using System.Collections.Immutable;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using Pal.Compiler.Ir;

namespace Pal.Compiler.Frontend;

/// <summary>Attribute queries shared by the collector and the lowerers.</summary>
public static class Declarations
{
    /// <summary>
    /// R4.13. The callee's parameter types in argument order, so that Emit can decide per
    /// argument whether C#'s implicit conversion into the mathematical world applies. A
    /// receiver occupies the leading slot and has no declared parameter, so it is null;
    /// so is any parameter whose type the frontend could not map.
    /// </summary>
    public static ImmutableArray<IrType?> ParamTypes(
        IMethodSymbol method, WellKnown known, bool receiver)
    {
        var declared = method.Parameters.Select(p => known.MapType(p.Type));
        return receiver ? [null, .. declared] : [.. declared];
    }

    public static bool Has(ISymbol symbol, INamedTypeSymbol attribute) =>        symbol.GetAttributes().Any(a =>
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

    /// <summary>The first string argument of a named attribute on a symbol, if present.</summary>
    public static string? StringArgument(ISymbol symbol, INamedTypeSymbol attribute) =>
        Find(symbol, attribute) is { } data ? StringArgument(data) : null;

    /// <summary>A named string property set on an attribute application.</summary>
    public static string? NamedString(AttributeData data, string name) =>
        data.NamedArguments.FirstOrDefault(a => a.Key == name).Value.Value as string;

    /// <summary>A named boolean property set on an attribute application.</summary>
    public static bool NamedFlag(AttributeData data, string name) =>
        data.NamedArguments.Any(a => a.Key == name && a.Value.Value is true);

    /// <summary>
    /// Which of the three kinds of translatable declaration a method is, or
    /// <c>null</c> if it is not translatable at all.
    /// </summary>
    public static CalleeKind? KindOf(IMethodSymbol method, WellKnown known)
    {
        if (Has(method, known.SpecAttribute)) return CalleeKind.Spec;
        if (Has(method, known.LemmaAttribute)) return CalleeKind.Lemma;

        // R18.1. pal-csharp translates a whole program: a method emits a module, and a
        // call emits an `open` of it. A method the compilation does not *declare* — one
        // from the BCL or any referenced assembly — has no module and never will, so
        // accepting it here emitted a call into a file that is never generated.
        // `ReferenceEquals(a, b)` was the live case: `Func_Object_ReferenceEquals` has
        // never existed, and the program translated with no diagnostic at all.
        if (method.DeclaringSyntaxReferences.IsEmpty) return null;

        // R20.1. Under `[TranslateAnnotatedOnly]` a method is translated when it, or the
        // property it is the getter of, carries an annotation, or when its class is a
        // translated one. Everything else is ordinary code the translation does not see,
        // and a call to it is refused exactly as a call into another assembly is.
        if (known.AnnotatedOnly && !InAnnotatedScope(method, known)) return null;

        if (method is { IsStatic: true, MethodKind: MethodKind.Ordinary }) return CalleeKind.Method;

        // R20.1a. An annotated instance method of a class that is not translated is
        // translated *receiver-free*: the class has no model and no invariant, so there
        // is nothing for the receiver to carry, and the method is a function of its
        // parameters -- which is what it must be, since a read of the receiver's state is
        // refused (R18.1) like any other read of an untranslated object.
        if (known.AnnotatedOnly &&
            method is { IsStatic: false, MethodKind: MethodKind.Ordinary } &&
            method.ContainingType is { TypeKind: TypeKind.Class } plainOwner &&
            !known.HasModel(plainOwner))
            return CalleeKind.Method;

        // §4.5. An instance method or constructor of a translated class: it carries the
        // object's invariant, which is what makes it translatable at all. R9.20 adds the
        // getter of a computed property, which is a nullary instance method that C# spells
        // differently; every rule downstream of here already speaks about it.
        return method is { IsStatic: false,
                           MethodKind: MethodKind.Ordinary or MethodKind.Constructor
                                       or MethodKind.PropertyGet }
               && method.ContainingType is { TypeKind: TypeKind.Class } owner
               && known.HasModel(owner)
            ? CalleeKind.Method
            : null;
    }

    private static bool InAnnotatedScope(IMethodSymbol method, WellKnown known) =>
        IsAnnotated(method, known)
        || method.AssociatedSymbol is { } property && IsAnnotated(property, known)
        || method.ContainingType is { TypeKind: TypeKind.Class } owner && known.HasModel(owner);

    /// <summary>
    /// R4.11. Whether a method leaves its receiver's model unchanged, decided from the
    /// body rather than from an annotation.
    /// </summary>
    /// <remarks>
    /// The test is syntactic but it <em>follows calls</em>, because R3.10b made the
    /// one-level version useless: an owner reads its state by calling its sub-objects'
    /// read-only methods, so a rule that counted any instance call as a mutation would
    /// classify every such reader as a mutator, and its caller would be handed a result
    /// related to a model it knows nothing about. That is not a conservative
    /// approximation, it is a useless answer.
    ///
    /// Recursion is bounded by treating a cycle as mutating. Getting this wrong in the
    /// permissive direction would be unsound — a caller would be told the model did not
    /// move when it did — so every case that is not demonstrably read-only is not.
    /// </remarks>
    public static bool IsReadOnly(IMethodSymbol method, Compilation compilation) =>
        IsReadOnly(method, compilation, new HashSet<IMethodSymbol>(SymbolEqualityComparer.Default));

    private static bool IsReadOnly(
        IMethodSymbol method, Compilation compilation, HashSet<IMethodSymbol> visiting)
    {
        if (method.MethodKind == MethodKind.Constructor) return false;

        // R9.7/R4.11b. An abstract method has no body, so there is no write set to read
        // the answer off: `[Frac]` on the declaration is what says it, exactly as R4.9a
        // says it of a parameter. Falling through to the syntax scan would find no
        // assignment in a declaration that has no statements at all and call every
        // virtual method read-only — including the mutating ones.
        if (method.IsAbstract)
            return method.GetAttributes().Any(a => a.AttributeClass?.Name == "FracAttribute");

        // A method already on the stack is one this analysis cannot finish, and an
        // unfinished answer is a mutating one.
        if (!visiting.Add(method.OriginalDefinition)) return false;
        try
        {
            var syntax = method.DeclaringSyntaxReferences.FirstOrDefault()?.GetSyntax();
            if (syntax is null || !compilation.ContainsSyntaxTree(syntax.SyntaxTree)) return false;
            var model = compilation.GetSemanticModel(syntax.SyntaxTree);

            return !Mutates(syntax, model, visiting);
        }
        finally
        {
            visiting.Remove(method.OriginalDefinition);
        }
    }

    /// <summary>
    /// Whether a body moves an object's model. Three ways: assigning an instance field,
    /// writing through one — an element of an array the object owns is as much a part of
    /// its model as a scalar field is (R3.10a) — and calling an instance method or handing
    /// an owned array to a callee that might write it.
    /// </summary>
    public static bool Mutates(SyntaxNode syntax, SemanticModel model) =>
        Mutates(syntax, model, new HashSet<IMethodSymbol>(SymbolEqualityComparer.Default));

    private static bool Mutates(
        SyntaxNode syntax, SemanticModel model, HashSet<IMethodSymbol> visiting)
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
                        { IsStatic: false, MethodKind: MethodKind.Ordinary } callee &&
                    !IsReadOnly(callee, model.Compilation, visiting))
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
    /// R9.20: whether a declaration carries an annotation that <em>classifies</em> it —
    /// <c>[Model]</c>, <c>[Spec]</c>, <c>[Lemma]</c>, <c>[Plain]</c> — as opposed to one
    /// that merely specifies it, like <c>[Requires]</c>. A computed property may carry a
    /// contract and still be a computed property; one that is a `[Spec]` observation is a
    /// different construct entirely.
    /// </summary>
    public static bool IsAnnotatedDeclaration(ISymbol symbol, WellKnown known) =>
        Has(symbol, known.ModelAttribute)
        || Has(symbol, known.SpecAttribute)
        || Has(symbol, known.LemmaAttribute)
        || Has(symbol, known.PlainAttribute);

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
