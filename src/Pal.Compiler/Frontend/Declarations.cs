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
            !known.HasModel(plainOwner) && !known.IsRegionClass(plainOwner))
            return CalleeKind.Method;

        // R27.16. A member of a `[Region]` class is a function of the object and the region.
        if (method is { IsStatic: false,
                        MethodKind: MethodKind.Ordinary or MethodKind.PropertyGet or MethodKind.PropertySet } &&
            known.IsRegionClass(method.ContainingType))
            return CalleeKind.Method;

        // R28.2. A member of a struct that borrows an enclosing object is a member of that
        // object's class: it carries the class's invariant, read-only.
        if (Borrowing.IsMember(method, known)) return CalleeKind.Method;

        // §4.5. An instance method or constructor of a translated class: it carries the
        // object's invariant, which is what makes it translatable at all. R9.20 adds the
        // getter of a computed property, which is a nullary instance method that C# spells
        // differently; every rule downstream of here already speaks about it.
        // R29.4. An explicit interface implementation (`IEnumerator IEnumerable.GetEnumerator()`)
        // is one when it carries a contract: nothing calls it, but it is code to verify.
        return (method is { IsStatic: false,
                            MethodKind: MethodKind.Ordinary or MethodKind.Constructor
                                        or MethodKind.PropertyGet or MethodKind.PropertySet } ||
                method is { IsStatic: false, MethodKind: MethodKind.ExplicitInterfaceImplementation } &&
                IsAnnotated(method, known))
               && method.ContainingType is { TypeKind: TypeKind.Class } owner
               && known.HasModel(owner)
            ? CalleeKind.Method
            : null;
    }

    // R22.3. Membership of a class with a model is not itself a request: a class verified
    // in place is verified member by member, and an unannotated member is outside the scope.
    private static bool InAnnotatedScope(IMethodSymbol method, WellKnown known) =>
        IsAnnotated(method, known)
        || method.AssociatedSymbol is { } property && IsAnnotated(property, known)
        // R32.13. A view's override of a member of its base with a contract at the view
        // (`At`) is checked against it.
        || method.IsOverride && Borrowing.ViewBase(method.ContainingType, known) is not null &&
           method.OverriddenMethod is { } o && HasViewContract(o, method.ContainingType);

    /// <summary>R32.13. Whether <paramref name="method"/> (or its property) has a contract clause <c>At</c> <paramref name="view"/>.</summary>
    private static bool HasViewContract(IMethodSymbol method, INamedTypeSymbol view) =>
        method.GetAttributes().Concat(method.AssociatedSymbol?.GetAttributes() ?? [])
            .Any(a => a.NamedArguments.Any(n => n.Key == "At" && n.Value.Value is INamedTypeSymbol at &&
                SymbolEqualityComparer.Default.Equals(at.OriginalDefinition, view.OriginalDefinition)));

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
    public static bool IsReadOnly(IMethodSymbol method, Compilation compilation, WellKnown? known = null) =>
        IsReadOnly(method, compilation, new HashSet<IMethodSymbol>(SymbolEqualityComparer.Default), known);

    private static bool IsReadOnly(
        IMethodSymbol method, Compilation compilation, HashSet<IMethodSymbol> visiting, WellKnown? known)
    {
        if (method.MethodKind == MethodKind.Constructor) return false;

        // R9.7/R4.11b. An abstract method has no body, so there is no write set to read
        // the answer off: `[Frac]` on the declaration is what says it, exactly as R4.9a
        // says it of a parameter. Falling through to the syntax scan would find no
        // assignment in a declaration that has no statements at all and call every
        // virtual method read-only — including the mutating ones.
        if (method.IsAbstract)
            return method.GetAttributes().Any(a => a.AttributeClass?.Name == "FracAttribute");
        // R32.2. So does it on a method with a body, as the method's own signature has it
        // (FrontendPass): R4.11c has F* check that body read-only.
        if (method.MethodKind == MethodKind.Ordinary &&
            method.OriginalDefinition.GetAttributes().Any(a => a.AttributeClass?.Name == "FracAttribute"))
            return true;

        // A method already on the stack is one this analysis cannot finish, and an
        // unfinished answer is a mutating one.
        if (!visiting.Add(method.OriginalDefinition)) return false;
        try
        {
            var syntax = method.DeclaringSyntaxReferences.FirstOrDefault()?.GetSyntax();
            if (syntax is null || !compilation.Owns(syntax.SyntaxTree)) return false;
            var model = compilation.Model(syntax.SyntaxTree);

            return !Mutates(syntax, model, visiting, known);
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
    public static bool Mutates(SyntaxNode syntax, SemanticModel model, WellKnown? known = null) =>
        Mutates(syntax, model, new HashSet<IMethodSymbol>(SymbolEqualityComparer.Default), known);

    /// <summary>R30.29. Whether a node of <paramref name="scope"/> that <paramref name="at"/> accepts moves an object's model.</summary>
    public static bool MutatesAt(SyntaxNode scope, Func<SyntaxNode, bool> at, SemanticModel model, WellKnown? known) =>
        Mutates(scope.DescendantNodes().Where(at), scope, model, new HashSet<IMethodSymbol>(SymbolEqualityComparer.Default), known);

    private static bool Mutates(
        SyntaxNode syntax, SemanticModel model, HashSet<IMethodSymbol> visiting, WellKnown? known) =>
        Mutates(syntax.DescendantNodes(), syntax, model, visiting, known);

    private static bool Mutates(
        IEnumerable<SyntaxNode> nodes, SyntaxNode syntax, SemanticModel model, HashSet<IMethodSymbol> visiting, WellKnown? known)
    {
        foreach (var node in nodes)
        {
            // R29.3b. Filling a view cache writes a field outside the representation.
            if (known is not null && node is AssignmentExpressionSyntax fill &&
                Borrowing.IsViewCacheFill(fill, model, known))
                continue;
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

            // R33.10. An element written through a local array may be one of a field's
            // (R24.19's `T[] nodes = _nodes;`), unless every value the local takes is fresh.
            if (target is ElementAccessExpressionSyntax &&
                model.GetSymbolInfo(RootOf(target)).Symbol is ILocalSymbol { Type: IArrayTypeSymbol } arrayLocal &&
                !AlwaysFresh(arrayLocal, syntax, model))
                return true;

            // R33.14. A write through a `ref` local writes what it aliases, which may be an
            // element of a field's array (R24.8, `ref int bucket = ref GetBucket(h)`).
            // Rebinding it (`entry = ref entries[i]`) writes nothing.
            if (target is not null &&
                node is not AssignmentExpressionSyntax { Right: RefExpressionSyntax } &&
                model.GetSymbolInfo(RootOf(target)).Symbol is ILocalSymbol { RefKind: RefKind.Ref })
                return true;

            // R27.16. An auto-property of a class is a field (R27.3), however it is written.
            if (target is not null &&
                model.GetSymbolInfo(RootOf(target)).Symbol is IPropertySymbol
                    { IsStatic: false, ContainingType.TypeKind: TypeKind.Class } auto &&
                auto.ContainingType.GetMembers().OfType<IFieldSymbol>()
                    .Any(f => SymbolEqualityComparer.Default.Equals(f.AssociatedSymbol, auto.OriginalDefinition)))
                return true;

            // R22.21. Assigning an instance property is a call of its setter.
            if (target is not null &&
                model.GetSymbolInfo(target).Symbol is IPropertySymbol { IsStatic: false, SetMethod: { } setter } &&
                !IsReadOnly(setter, model.Compilation, visiting, known))
                return true;

            if (node is InvocationExpressionSyntax call)
            {
                // R30.29. `Unsafe.IsNullRef(ref r)` only tests the reference.
                if (model.GetSymbolInfo(call).Symbol is IMethodSymbol isNull && RefSnapshots.IsIsNullRef(isNull))
                    continue;
                // R27.41. A member of a borrowing struct held in a local writes the local,
                // and takes the object it borrows read-only.
                if (known is not null && model.GetSymbolInfo(call).Symbol is IMethodSymbol held &&
                    Borrowing.IsMember(held, known) &&
                    call.Expression is MemberAccessExpressionSyntax { Expression: IdentifierNameSyntax heldLocal } &&
                    model.GetSymbolInfo(heldLocal).Symbol is ILocalSymbol &&
                    // R32.13. Unless it is a view's member that writes the object it borrows.
                    !(Borrowing.IsView(held.ContainingType, known) &&
                      held.OriginalDefinition.DeclaringSyntaxReferences.FirstOrDefault()?.GetSyntax() is { } heldBody &&
                      Borrowing.WritesOwner(heldBody, model.Compilation.Model(heldBody.SyntaxTree),
                          held.ContainingType.OriginalDefinition, known)))
                    continue;
                // R30.26 / R33.14. A `[SpecBinding]`-bound library method (a comparer's `Equals`) is an
                // F* term, which cannot reach this object's state except through an array
                // argument, checked below.
                if (model.GetSymbolInfo(call).Symbol is IMethodSymbol
                        { IsStatic: false, MethodKind: MethodKind.Ordinary } callee &&
                    known?.Binding(callee) is null &&
                    !IsReadOnly(callee, model.Compilation, visiting, known))
                    return true;

                // An owned array handed to a callee may come back written. Assuming it
                // does is the strict direction, and the strict direction costs a caller an
                // existential; the permissive one would be a lie.
                // R22.25. Except where R22.25 models the callee as a search, which takes
                // the array read-only; and R25.5's binary search.
                if (model.GetSymbolInfo(call).Symbol is IMethodSymbol
                    {
                        Name: "IndexOf" or "LastIndexOf" or "BinarySearch",
                        ContainingType: { Name: "Array", ContainingNamespace.Name: "System" },
                    })
                    continue;
                // R33.14. A specification intrinsic (`Pal.Contents(_a)`), and a `[Spec]` or
                // `[Lemma]` member, is ghost: it reads the array it is handed.
                if (known is not null && model.GetSymbolInfo(call).Symbol is IMethodSymbol ghost &&
                    (SymbolEqualityComparer.Default.Equals(ghost.ContainingType, known.Pal) ||
                     Has(ghost, known.SpecAttribute) || Has(ghost, known.LemmaAttribute)))
                    continue;
                foreach (var argument in call.ArgumentList.Arguments)
                {
                    if (model.GetSymbolInfo(RootOf(argument.Expression)).Symbol
                            is IFieldSymbol { IsStatic: false, Type: IArrayTypeSymbol })
                        return true;
                    // R33.24. A `ref` argument the callee may write through: a `ref` local
                    // (R33.16's `ref entry` into a field's array) or a field itself.
                    if (argument.RefKindKeyword.RawKind is (int)SyntaxKind.RefKeyword or (int)SyntaxKind.OutKeyword &&
                        model.GetSymbolInfo(RootOf(argument.Expression)).Symbol
                            is ILocalSymbol { RefKind: RefKind.Ref } or IFieldSymbol { IsStatic: false })
                        return true;
                }
            }
        }
        return false;
    }

    /// <summary>
    /// R33.10. Whether every value <paramref name="local"/> takes in <paramref name="body"/>
    /// is a newly created array, so that writing its elements writes no object's field.
    /// </summary>
    private static bool AlwaysFresh(ILocalSymbol local, SyntaxNode body, SemanticModel model)
    {
        static bool Fresh(ExpressionSyntax? e) =>
            e is ArrayCreationExpressionSyntax or ImplicitArrayCreationExpressionSyntax or CollectionExpressionSyntax;
        if (local.DeclaringSyntaxReferences is not [var decl] || decl.GetSyntax() is not VariableDeclaratorSyntax ||
            local.IsRef)
            return false;
        foreach (var node in body.DescendantNodes())
        {
            if (node is VariableDeclaratorSyntax v &&
                SymbolEqualityComparer.Default.Equals(model.GetDeclaredSymbol(v), local) &&
                !Fresh(v.Initializer?.Value))
                return false;
            if (node is AssignmentExpressionSyntax a &&
                SymbolEqualityComparer.Default.Equals(model.GetSymbolInfo(a.Left).Symbol, local) &&
                !(a.IsKind(SyntaxKind.SimpleAssignmentExpression) && Fresh(a.Right)))
                return false;
            if (node is ArgumentSyntax { RefKindKeyword.RawKind: not 0 } arg &&
                SymbolEqualityComparer.Default.Equals(model.GetSymbolInfo(arg.Expression).Symbol, local))
                return false;
        }
        return true;
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
    /// <summary>
    /// R20.12. Whether <paramref name="method"/> is translated receiver-free (R20.1a): an
    /// annotated instance method of a class with no model, under
    /// <c>[TranslateAnnotatedOnly]</c>.
    /// </summary>
    public static bool IsReceiverFree(IMethodSymbol method, WellKnown known) =>
        known.AnnotatedOnly &&
        method is { IsStatic: false, MethodKind: MethodKind.Ordinary } &&
        method.ContainingType is { TypeKind: TypeKind.Class } owner &&
        !known.HasModel(owner) && !known.IsRegionClass(owner);

    /// <summary>The R20.12 name a context field is bound to in a receiver-free method.</summary>
    public static string ContextName(ISymbol field) => "this__" + field.Name;

    /// <summary>The type of a context value: a field's, or a captured parameter's (R20.12a).</summary>
    public static ITypeSymbol ContextType(ISymbol field) => field switch
    {
        IFieldSymbol f => f.Type,
        IParameterSymbol p => p.Type,
        _ => throw new ArgumentException($"not a context value: {field}"),
    };

    /// <summary>
    /// R20.12a. The parameters of <paramref name="owner"/>'s primary constructor that its
    /// members capture and nothing assigns. Each holds the value the constructor was given
    /// for as long as the object lives, exactly as a <c>readonly</c> field does.
    /// </summary>
    public static IEnumerable<IParameterSymbol> CapturedParameters(INamedTypeSymbol owner, Compilation compilation)
    {
        foreach (var ctor in owner.InstanceConstructors)
        {
            if (ctor.DeclaringSyntaxReferences.FirstOrDefault()?.GetSyntax() is not TypeDeclarationSyntax decl)
                continue;
            var model = compilation.Model(decl.SyntaxTree);
            foreach (var p in ctor.Parameters)
            {
                var assigned = decl.DescendantNodes().Any(n =>
                    n is AssignmentExpressionSyntax a &&
                    SymbolEqualityComparer.Default.Equals(model.GetSymbolInfo(a.Left).Symbol, p) ||
                    n is PrefixUnaryExpressionSyntax or PostfixUnaryExpressionSyntax &&
                    n.ChildNodes().Any(c => SymbolEqualityComparer.Default.Equals(model.GetSymbolInfo(c).Symbol, p)) ||
                    n is ArgumentSyntax { RefKindKeyword.RawKind: not 0 } arg &&
                    SymbolEqualityComparer.Default.Equals(model.GetSymbolInfo(arg.Expression).Symbol, p));
                if (!assigned) yield return p;
            }
        }
    }

    private static readonly System.Runtime.CompilerServices.ConditionalWeakTable<
        INamedTypeSymbol, System.Runtime.CompilerServices.StrongBox<ImmutableArray<ISymbol>>> contextFields = new();

    /// <summary>
    /// R20.12. The <c>readonly</c> instance fields of <paramref name="owner"/> that its
    /// receiver-free methods read, in declaration order. Each is a parameter of every one
    /// of those methods: the receiver is the same object throughout a chain of such calls,
    /// and a `readonly` field of it is assigned only by its constructor, so each method
    /// sees the same value. A field is read when an annotated instance method's body
    /// names it, or a contract of one mentions it.
    /// </summary>
    public static ImmutableArray<ISymbol> ContextFields(
        INamedTypeSymbol owner, Compilation compilation, WellKnown known) =>
        contextFields.GetValue(owner, o => new(ComputeContextFields(o, compilation, known))).Value;

    private static ImmutableArray<ISymbol> ComputeContextFields(
        INamedTypeSymbol owner, Compilation compilation, WellKnown known)
    {
        var candidates = owner.GetMembers().OfType<IFieldSymbol>()
            .Where(f => f is { IsStatic: false, IsReadOnly: true, IsImplicitlyDeclared: false } &&
                        known.MapType(f.Type) is not null)
            .Cast<ISymbol>()
            .Concat(CapturedParameters(owner, compilation).Where(p => known.MapType(p.Type) is not null))
            .ToList();
        if (candidates.Count == 0) return [];
        var read = new HashSet<ISymbol>(SymbolEqualityComparer.Default);
        foreach (var m in owner.GetMembers().OfType<IMethodSymbol>())
        {
            if (!IsReceiverFree(m, known) || !IsAnnotated(m, known) || Has(m, known.AdmitAttribute))
                continue;
            foreach (var reference in m.DeclaringSyntaxReferences)
            {
                var syntax = reference.GetSyntax();
                var model = compilation.Model(syntax.SyntaxTree);
                foreach (var id in syntax.DescendantNodes().OfType<IdentifierNameSyntax>())
                    if (model.GetSymbolInfo(id).Symbol is IFieldSymbol or IParameterSymbol &&
                        model.GetSymbolInfo(id).Symbol is { } f &&
                        candidates.Contains(f, SymbolEqualityComparer.Default))
                        read.Add(f);
            }
            foreach (var a in m.GetAttributes())
                foreach (var arg in a.ConstructorArguments)
                    if (arg.Value is string text)
                        foreach (var f in candidates)
                            if (System.Text.RegularExpressions.Regex.IsMatch(
                                    text, $@"(?<![\w.]){f.Name}\b"))
                                read.Add(f);
        }
        return [.. candidates.Where(read.Contains)];
    }

    /// <summary>
    /// R20.12. The <c>static readonly</c> fields of <paramref name="method"/>'s class that its
    /// own contracts mention.
    /// </summary>
    public static ImmutableArray<IFieldSymbol> ContractStatics(IMethodSymbol method, WellKnown known)
    {
        var texts = method.GetAttributes()
            .Where(a => a.AttributeClass is { ContainingNamespace.Name: WellKnown.Namespace })
            .SelectMany(a => a.ConstructorArguments)
            .Select(arg => arg.Value as string)
            .OfType<string>()
            .ToList();
        return [.. method.ContainingType.GetMembers().OfType<IFieldSymbol>()
            .Where(f => f is { IsStatic: true, IsReadOnly: true, IsImplicitlyDeclared: false } &&
                        known.MapType(f.Type) is not null &&
                        texts.Any(t => System.Text.RegularExpressions.Regex.IsMatch(
                            t, $@"(?<![\w.]){f.Name}\b")))];
    }

    /// <summary>
    /// R20.13. The <c>[SpecOp]</c> function of an indexer's setter, when the indexer has
    /// one: a write through it is a functional update of the receiver's value.
    /// </summary>
    public static string? SpecSetter(ISymbol? symbol, WellKnown known) =>
        symbol is IPropertySymbol { IsIndexer: true, SetMethod: { } set } ? known.SpecOpName(set) : null;

    private static readonly System.Runtime.CompilerServices.ConditionalWeakTable<
        IParameterSymbol, System.Runtime.CompilerServices.StrongBox<bool>> written = new();

    [ThreadStatic] private static HashSet<IParameterSymbol>? writtenInProgress;

    /// <summary>
    /// R20.13. Whether a by-value parameter of a specification type is <em>written</em>:
    /// its method stores through a <c>[SpecOp]</c> indexer setter on it, or passes it to a
    /// parameter that is written. Such a parameter is translated as <c>ref</c>, because the
    /// object the caller holds is the one that changes.
    /// </summary>
    public static bool IsWritten(IParameterSymbol p, Compilation compilation, WellKnown known)
    {
        if (p.RefKind != RefKind.None || known.SpecTypeName(p.Type) is null ||
            p.ContainingSymbol is not IMethodSymbol method ||
            !IsAnnotated(method, known) || Has(method, known.AdmitAttribute))
            return false;
        if (written.TryGetValue(p, out var box)) return box.Value;

        var top = writtenInProgress is null;
        writtenInProgress ??= new HashSet<IParameterSymbol>(SymbolEqualityComparer.Default);
        if (!writtenInProgress.Add(p)) return false;
        try
        {
            var result = ComputeWritten(p, method, compilation, known);
            // A result that depended on a parameter still being computed may be too
            // small; only an outermost one is final.
            if (top) { written.Remove(p); written.Add(p, new(result)); }
            return result;
        }
        finally
        {
            writtenInProgress.Remove(p);
            if (top) writtenInProgress = null;
        }
    }

    private static bool ComputeWritten(
        IParameterSymbol p, IMethodSymbol method, Compilation compilation, WellKnown known)
    {
        foreach (var reference in method.DeclaringSyntaxReferences)
        {
            var syntax = reference.GetSyntax();
            var model = compilation.Model(syntax.SyntaxTree);
            // By declaration, not by symbol: `p` may come from another compilation of the
            // same trees (the one the spec shims were added to).
            bool Names(ExpressionSyntax e) =>
                e is IdentifierNameSyntax id &&
                model.GetSymbolInfo(id).Symbol is IParameterSymbol q &&
                q.Locations.SequenceEqual(p.Locations);
            foreach (var n in syntax.DescendantNodes())
            {
                if (n is AssignmentExpressionSyntax { Left: ElementAccessExpressionSyntax ea } &&
                    Names(ea.Expression) && SpecSetter(model.GetSymbolInfo(ea).Symbol, known) is not null)
                    return true;
                if (n is ArgumentSyntax arg && Names(arg.Expression) &&
                    WrittenParameterOf(arg, model, known) is not null)
                    return true;
            }
        }
        return false;
    }

    /// <summary>R20.13. The written parameter an argument is passed to, if it is one.</summary>
    public static IParameterSymbol? WrittenParameterOf(ArgumentSyntax arg, SemanticModel model, WellKnown known) =>
        model.GetOperation(arg) is Microsoft.CodeAnalysis.Operations.IArgumentOperation { Parameter: { } target } &&
        IsWritten(target, model.Compilation, known)
            ? target
            : null;

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
        || Has(symbol, known.PlainAttribute)
        || Has(symbol, known.RegionAttribute);

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
