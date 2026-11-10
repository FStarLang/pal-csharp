using System.Collections.Immutable;
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
        // R32.13. So does a view: a sealed class nested in the class with a model it
        // derives from, declaring no model of its own.
        if (!(s.TypeKind == TypeKind.Struct ||
              s is { TypeKind: TypeKind.Class, IsSealed: true, IsStatic: false, BaseType.SpecialType: SpecialType.System_Object } &&
              !known.HasModel(s.OriginalDefinition) && !Declarations.Has(s.OriginalDefinition, known.PlainAttribute) ||
              ViewBase(s, known) is not null))
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
    /// R32.13. The class a *view* derives from: <paramref name="type"/> is a sealed class
    /// nested in a class with a model that is also its direct base, and declares no model
    /// of its own (it may not be <c>[Plain]</c>). The view's state is the record of its own
    /// fields and the base's instance fields; it borrows the object its readonly field of
    /// the base type holds (R28.1), and is verified at its exact type.
    /// </summary>
    public static INamedTypeSymbol? ViewBase(ITypeSymbol? type, WellKnown known) =>
        type is INamedTypeSymbol { TypeKind: TypeKind.Class, IsSealed: true, IsStatic: false, BaseType: { } b } s &&
        b.SpecialType != SpecialType.System_Object && Encloses(b, s) &&
        !s.OriginalDefinition.GetMembers().Any(m => Declarations.Has(m, known.ModelAttribute)) &&
        !Declarations.Has(s.OriginalDefinition, known.PlainAttribute) &&
        b.OriginalDefinition.GetMembers().Any(m => Declarations.Has(m, known.ModelAttribute)) &&
        (Declarations.IsAnnotated(s.OriginalDefinition, known) ||
         s.OriginalDefinition.GetMembers().Any(m => Declarations.IsAnnotated(m, known) ||
             m is IMethodSymbol { AssociatedSymbol: { } a } && Declarations.IsAnnotated(a, known)))
            ? b : null;

    /// <summary>R32.13. Whether <paramref name="type"/> is a view (<see cref="ViewBase"/>).</summary>
    public static bool IsView(ITypeSymbol? type, WellKnown known) => ViewBase(type, known) is not null;

    /// <summary>
    /// R28.1, R32.13. Whether <paramref name="f"/> is a field of the state of the borrowing
    /// type <paramref name="self"/>: one it declares, or, for a view, one its base declares.
    /// </summary>
    public static bool IsStateField(IFieldSymbol f, INamedTypeSymbol self, WellKnown? known)
    {
        if (f.IsStatic || f.IsConst) return false;
        var holder = f.ContainingType.OriginalDefinition;
        if (SymbolEqualityComparer.Default.Equals(holder, self.OriginalDefinition)) return true;
        return known is not null && ViewBase(self, known) is { } b &&
               SymbolEqualityComparer.Default.Equals(holder, b.OriginalDefinition);
    }

    /// <summary>R32.13. The base's instance fields in a view's record: the ones the base's own representation maps.</summary>
    public static IEnumerable<IFieldSymbol> InheritedState(INamedTypeSymbol self, WellKnown known) =>
        ViewBase(self, known) is { } b
            ? b.GetMembers().OfType<IFieldSymbol>().Where(f =>
                !f.IsStatic && !f.IsConst && f.AssociatedSymbol is null && known.MapType(f.Type) is not null &&
                !IsBorrowingClass(f.Type, known))
            : [];

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
    /// R32.12. The wrapped field of a *wrapping* struct: a struct that borrows nothing itself
    /// (R28.1), whose one instance field of struct type is a borrowing or wrapping struct,
    /// and whose other instance fields are values that hold no reference.
    /// </summary>
    public static IFieldSymbol? InnerField(ITypeSymbol? type, WellKnown known) => InnerField(type, known, 0);

    private static IFieldSymbol? InnerField(ITypeSymbol? type, WellKnown known, int depth)
    {
        if (depth > 8 || type is not INamedTypeSymbol { TypeKind: TypeKind.Struct } s || OwnerField(s, known) is not null)
            return null;
        IFieldSymbol? found = null;
        foreach (var f in s.GetMembers().OfType<IFieldSymbol>())
        {
            if (f.IsStatic || f.IsConst) continue;
            if (f.Type is INamedTypeSymbol { TypeKind: TypeKind.Struct } ft &&
                (IsBorrowing(ft, known) || InnerField(ft, known, depth + 1) is not null))
            {
                if (found is not null) return null;
                found = f;
                continue;
            }
            if (f.Type.IsReferenceType || f.Type.TypeKind == TypeKind.TypeParameter ||
                f.Type is { TypeKind: TypeKind.Struct, SpecialType: SpecialType.None }) return null;
        }
        return found;
    }

    /// <summary>R32.12. Whether <paramref name="type"/> is a wrapping struct.</summary>
    public static bool IsWrapping(ITypeSymbol? type, WellKnown known) => InnerField(type, known) is not null;

    /// <summary>
    /// R35.3. A wrapping struct that may be created: it wraps its core directly, and the core
    /// owns no objects, so the core a method of the owner's class returns is all it holds.
    /// </summary>
    public static bool CreatableWrapping(ITypeSymbol? type, WellKnown known) =>
        type is not null && IsWrapping(type, known) && Innermost(type, known) is { Path.Length: 1, Core: var core } &&
        OwnedFields(core, known).IsEmpty;

    /// <summary>
    /// R32.12. The wrapped fields from a wrapping struct down to the borrowing struct at its
    /// core, and that struct: each field is of the struct the next is a field of.
    /// </summary>
    public static (ImmutableArray<IFieldSymbol> Path, INamedTypeSymbol Core) Innermost(ITypeSymbol type, WellKnown known)
    {
        var path = ImmutableArray.CreateBuilder<IFieldSymbol>();
        var t = (INamedTypeSymbol)type;
        while (InnerField(t, known) is { } f)
        {
            path.Add(f);
            t = (INamedTypeSymbol)f.Type;
        }
        return (path.ToImmutable(), t);
    }

    /// <summary>
    /// R28.2. Whether <paramref name="method"/> is a member of a borrowing struct that is
    /// translated: an instance method, accessor, constructor, or explicit interface
    /// implementation.
    /// </summary>
    public static bool IsMember(IMethodSymbol method, WellKnown known) =>
        method is { IsStatic: false,
                    MethodKind: MethodKind.Ordinary or MethodKind.Constructor or MethodKind.PropertyGet or MethodKind.PropertySet
                                or MethodKind.ExplicitInterfaceImplementation }
        && (IsBorrowing(method.ContainingType, known) || IsWrapping(method.ContainingType, known));

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
            // R32.12. A call of a writer member of the struct a wrapping struct wraps writes it.
            if (node is InvocationExpressionSyntax
                {
                    Expression: MemberAccessExpressionSyntax
                    {
                        Expression: var wrapped and (IdentifierNameSyntax or MemberAccessExpressionSyntax { Expression: ThisExpressionSyntax }),
                    },
                } inner &&
                model.GetSymbolInfo(wrapped).Symbol is IFieldSymbol { IsStatic: false, Type: INamedTypeSymbol { TypeKind: TypeKind.Struct } wt } wf &&
                SymbolEqualityComparer.Default.Equals(wf.ContainingType.OriginalDefinition, self.OriginalDefinition) &&
                model.GetSymbolInfo(inner).Symbol is IMethodSymbol { IsStatic: false } innerCallee &&
                SymbolEqualityComparer.Default.Equals(innerCallee.ContainingType.OriginalDefinition, wt.OriginalDefinition) &&
                innerCallee.DeclaringSyntaxReferences.FirstOrDefault()?.GetSyntax() is { } innerDecl &&
                model.Compilation.ContainsSyntaxTree(innerDecl.SyntaxTree) &&
                WritesState(innerDecl, model.Compilation.GetSemanticModel(innerDecl.SyntaxTree), wt, seen))
                return true;
            var target = node switch
            {
                AssignmentExpressionSyntax a => a.Left,
                PrefixUnaryExpressionSyntax p when IsStep(p) => p.Operand,
                PostfixUnaryExpressionSyntax p when IsStep(p) => p.Operand,
                // R35.4. A field passed by reference may be written.
                ArgumentSyntax { RefKindKeyword.RawKind: (int)SyntaxKind.RefKeyword or (int)SyntaxKind.OutKeyword } ra => ra.Expression,
                _ => null,
            };
            if (target is null) continue;
            while (target is ParenthesizedExpressionSyntax pe) target = pe.Expression;
            if (target is MemberAccessExpressionSyntax { Expression: ThisExpressionSyntax } or IdentifierNameSyntax &&
                (model.GetSymbolInfo(target).Symbol is IFieldSymbol { IsStatic: false } f &&
                 SymbolEqualityComparer.Default.Equals(f.ContainingType.OriginalDefinition, self.OriginalDefinition) ||
                 IsAutoProperty(model.GetSymbolInfo(target).Symbol, self)))
                return true;
        }
        return false;
    }

    /// <summary>
    /// R32.14. The names of the view's state fields (its own and its base's) a member of the
    /// view may write: by assignment, step or <c>ref</c> argument in its body, or in the
    /// body of a member of the view or its base it calls or reads on itself (bound at the
    /// view: an override of the view's, else the base's), transitively. Lambdas' bodies are
    /// part of the body they are written in.
    /// </summary>
    public static HashSet<string> ViewWrites(SyntaxNode body, SemanticModel model, INamedTypeSymbol view, WellKnown known)
    {
        var written = new HashSet<string>();
        ViewWrites(body, model, view, known, written, new HashSet<SyntaxNode>());
        return written;
    }

    private static void ViewWrites(SyntaxNode body, SemanticModel model, INamedTypeSymbol view, WellKnown known,
        HashSet<string> written, HashSet<SyntaxNode> seen)
    {
        if (!seen.Add(body) || ViewBase(view, known) is not { } vb) return;
        bool Ours(ISymbol m) =>
            SymbolEqualityComparer.Default.Equals(m.ContainingType.OriginalDefinition, view.OriginalDefinition) ||
            SymbolEqualityComparer.Default.Equals(m.ContainingType.OriginalDefinition, vb.OriginalDefinition);
        void Into(IMethodSymbol? callee, bool viaBase)
        {
            if (callee is null) return;
            var target = viaBase ? callee : Subclasses.OverrideOf(view, callee) ?? callee;
            foreach (var r in target.DeclaringSyntaxReferences)
                if (model.Compilation.ContainsSyntaxTree(r.SyntaxTree))
                    ViewWrites(r.GetSyntax(), model.Compilation.GetSemanticModel(r.SyntaxTree), view, known, written, seen);
        }
        foreach (var node in body.DescendantNodes())
        {
            var target = node switch
            {
                AssignmentExpressionSyntax a => a.Left,
                PrefixUnaryExpressionSyntax p when IsStep(p) => p.Operand,
                PostfixUnaryExpressionSyntax p when IsStep(p) => p.Operand,
                ArgumentSyntax { RefKindKeyword.RawKind: not 0 } arg => arg.Expression,
                _ => null,
            };
            if (target is not null)
            {
                while (target is ParenthesizedExpressionSyntax pe) target = pe.Expression;
                if (target is IdentifierNameSyntax or MemberAccessExpressionSyntax { Expression: ThisExpressionSyntax or BaseExpressionSyntax } &&
                    model.GetSymbolInfo(target).Symbol is IFieldSymbol { IsStatic: false } f && Ours(f))
                    written.Add(f.Name);
            }
            // A member of the view reached on itself: an invocation, or a property read or written.
            if (node is not (IdentifierNameSyntax or MemberAccessExpressionSyntax) ||
                node.Parent is MemberAccessExpressionSyntax pm && pm.Name == node) continue;
            var receiver = node is MemberAccessExpressionSyntax ma ? ma.Expression : null;
            if (receiver is not (null or ThisExpressionSyntax or BaseExpressionSyntax)) continue;
            var viaBase = receiver is BaseExpressionSyntax;
            switch (model.GetSymbolInfo(node).Symbol)
            {
                case IMethodSymbol { IsStatic: false } m when Ours(m):
                    Into(m, viaBase);
                    break;
                case IPropertySymbol { IsStatic: false } prop when Ours(prop):
                    Into(prop.GetMethod, viaBase);
                    Into(prop.SetMethod, viaBase);
                    break;
            }
        }
    }

    /// <summary>
    /// R32.13. Whether a member of the view <paramref name="view"/> writes the object it
    /// borrows: it calls a method of it that is not read-only, or calls (on itself, or on
    /// <c>base</c>) a member of the view or its base that does, transitively.
    /// </summary>
    public static bool WritesOwner(SyntaxNode body, SemanticModel model, INamedTypeSymbol view, WellKnown known) =>
        WritesOwner(body, model, view, known, new HashSet<SyntaxNode>());

    private static bool WritesOwner(SyntaxNode body, SemanticModel model, INamedTypeSymbol view, WellKnown known,
        HashSet<SyntaxNode> seen)
    {
        if (!seen.Add(body) || ViewBase(view, known) is not { } vb || OwnerField(view, known) is not { } owner) return false;
        foreach (var node in body.DescendantNodes())
        {
            if (node is not InvocationExpressionSyntax call ||
                model.GetSymbolInfo(call).Symbol is not IMethodSymbol { IsStatic: false } callee) continue;
            var receiver = call.Expression is MemberAccessExpressionSyntax ma ? ma.Expression : null;
            if (receiver is not null && model.GetSymbolInfo(receiver).Symbol is IFieldSymbol rf &&
                SymbolEqualityComparer.Default.Equals(rf.OriginalDefinition, owner.OriginalDefinition))
            {
                if (!Declarations.IsReadOnly(callee, model.Compilation, known)) return true;
                continue;
            }
            if (receiver is not (null or ThisExpressionSyntax or BaseExpressionSyntax)) continue;
            var holder = callee.ContainingType.OriginalDefinition;
            if (!SymbolEqualityComparer.Default.Equals(holder, view.OriginalDefinition) &&
                !SymbolEqualityComparer.Default.Equals(holder, vb.OriginalDefinition)) continue;
            var target = receiver is BaseExpressionSyntax ? callee
                : Subclasses.OverrideOf(view, callee) ?? callee;
            foreach (var r in target.DeclaringSyntaxReferences)
                if (model.Compilation.ContainsSyntaxTree(r.SyntaxTree) &&
                    WritesOwner(r.GetSyntax(), model.Compilation.GetSemanticModel(r.SyntaxTree), view, known, seen))
                    return true;
        }
        return false;
    }

    /// <summary>
    /// R33.26. An instance auto-property of the struct (<c>Current { get; private set; }</c>):
    /// its backing field is one of the struct's fields (R3.4), under the property's name.
    /// </summary>
    public static bool IsAutoProperty(ISymbol? symbol, INamedTypeSymbol self) =>
        symbol is IPropertySymbol { IsStatic: false, IsIndexer: false } p &&
        SymbolEqualityComparer.Default.Equals(p.ContainingType.OriginalDefinition, self.OriginalDefinition) &&
        self.OriginalDefinition.GetMembers().OfType<IFieldSymbol>()
            .Any(f => SymbolEqualityComparer.Default.Equals(f.AssociatedSymbol, p.OriginalDefinition));

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
        // R32.13. A view's constructor calls its base's (`: base(u.Comparer)`) and then assigns
        // its fields, the borrowing one among them.
        if (decl.Initializer is { } init && !init.ThisOrBaseKeyword.IsKind(SyntaxKind.BaseKeyword))
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
        return compilation is null ? null : WrappingOwnerParameter(ctor, decl, owner, compilation);
    }

    /// <summary>
    /// R35.3. The parameter a wrapping struct's constructor takes the object its core borrows
    /// in: the receiver of the call that creates the wrapped struct
    /// (<c>_enumerator = dictionary.GetEnumerator()</c>), a method of the owner's class.
    /// </summary>
    private static IParameterSymbol? WrappingOwnerParameter(
        IMethodSymbol ctor, ConstructorDeclarationSyntax decl, IFieldSymbol owner, Compilation compilation)
    {
        if (ctor.ContainingType is not { TypeKind: TypeKind.Struct } self || decl.Initializer is not null) return null;
        var model = compilation.GetSemanticModel(decl.SyntaxTree);
        IEnumerable<ExpressionSyntax> exprs = decl.Body?.Statements.OfType<ExpressionStatementSyntax>()
            .Select(s => s.Expression) ?? [];
        if (decl.ExpressionBody is { } eb) exprs = [eb.Expression];
        foreach (var e in exprs)
        {
            if (e is not AssignmentExpressionSyntax { Left: var left, Right: var right } ||
                model.GetSymbolInfo(left).Symbol is not IFieldSymbol
                {
                    IsStatic: false, Type: INamedTypeSymbol { TypeKind: TypeKind.Struct },
                } wf ||
                wf.ContainingType.OriginalDefinition.ToDisplayString() != self.OriginalDefinition.ToDisplayString())
                continue;
            ExpressionSyntax? source = right switch
            {
                InvocationExpressionSyntax { Expression: MemberAccessExpressionSyntax { Expression: IdentifierNameSyntax recv } } => recv,
                _ => null,
            };
            if (source is IdentifierNameSyntax id && model.GetSymbolInfo(id).Symbol is IParameterSymbol p &&
                p.ContainingSymbol is IMethodSymbol { MethodKind: MethodKind.Constructor } &&
                p.Type.OriginalDefinition.ToDisplayString() == owner.Type.OriginalDefinition.ToDisplayString())
                return ctor.Parameters.FirstOrDefault(cp => cp.Name == p.Name);
        }
        return null;
    }
}
