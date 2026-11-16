using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using Pal.Compiler.Ir;

namespace Pal.Compiler.Frontend;

/// <summary>
/// §34. An <c>IEnumerable&lt;T&gt;</c> or <c>ICollection&lt;T&gt;</c> argument
/// (<see cref="IrEnumerableType"/>): the type test that dispatches on it, the members of
/// <c>ICollection&lt;T&gt;</c> the BCL's fast path calls, and the enumerator its slow path
/// walks, which is a cursor over the items the argument yields.
/// </summary>
public sealed partial class ExprLowerer
{
    // R34.6. The enumerator locals in scope, by name, with the enumerable each enumerates.
    private readonly Dictionary<string, IrExpr> _cursors = [];

    /// <summary>R34.6. <paramref name="name"/> is an enumerator of <paramref name="source"/> from here on.</summary>
    public void HoldCursor(string name, IrExpr source) => _cursors[name] = source;

    /// <summary>R34.6. The enumerator <paramref name="name"/> is out of scope.</summary>
    public void ReleaseCursor(string name) => _cursors.Remove(name);

    /// <summary>R34.6. The enumerable <paramref name="e"/> names an enumerator of, if it is one in scope.</summary>
    public (string Name, IrExpr Source)? CursorOf(ExpressionSyntax e) =>
        Unparenthesized(e) is IdentifierNameSyntax id &&
        model.GetSymbolInfo(id).Symbol is ILocalSymbol local &&
        _cursors.TryGetValue(local.Name, out var source)
            ? (local.Name, source)
            : null;

    /// <summary>
    /// §34. Whether <paramref name="e"/> names an enumerable argument: a parameter (or a
    /// local) of type <c>IEnumerable&lt;T&gt;</c> or <c>ICollection&lt;T&gt;</c>. Any other
    /// expression of such a type — <c>this</c> cast to an interface, say — is left alone.
    /// </summary>
    public bool IsEnumerableArgument(ExpressionSyntax e) =>
        Unparenthesized(e) is IdentifierNameSyntax id &&
        model.GetSymbolInfo(id).Symbol is IParameterSymbol or ILocalSymbol &&
        known.MapType(model.GetTypeInfo(id).Type) is IrEnumerableType &&
        // Not one an earlier rule rebinds (a pattern variable, an alias, a typed receiver).
        Unboxed(Lower(id)) is not { Type: not null and not IrEnumerableType };

    private static IrVar Cursor(IrLoc loc, string name) => new(loc, name) { Type = IrPrim.Int };

    // R34.20. The locals `var c = e as ICollection<T>;` binds, with the enumerable each names.
    private readonly Dictionary<ISymbol, IrExpr> _collectionAliases = new(SymbolEqualityComparer.Default);

    /// <summary>R34.20. <paramref name="local"/> is <paramref name="source"/> as an <c>ICollection&lt;T&gt;</c>, or null.</summary>
    public void CollectionAlias(ILocalSymbol local, IrExpr source)
    {
        _collectionAliases[local] = source;
        Alias(local, source);
    }

    /// <summary>R34.20. Whether <paramref name="e"/> names a local bound by <c>e as ICollection&lt;T&gt;</c>.</summary>
    public bool IsCollectionAlias(ExpressionSyntax e) =>
        Unparenthesized(e) is IdentifierNameSyntax id &&
        model.GetSymbolInfo(id).Symbol is ILocalSymbol local && _collectionAliases.ContainsKey(local);

    /// <summary>
    /// R34.20. <c>c == null</c>, <c>c is null</c> (and their negations) on such a local: the
    /// enumerable is not a collection (R34.4's <c>is_collection</c>).
    /// </summary>
    private IrExpr? CollectionAliasNullTest(ExpressionSyntax subject, bool isNull, IrLoc loc)
    {
        if (Unparenthesized(subject) is not IdentifierNameSyntax id ||
            model.GetSymbolInfo(id).Symbol is not ILocalSymbol local ||
            !_collectionAliases.TryGetValue(local, out var source)) return null;
        IrExpr test = new IrSpecOp(loc, "Pulse.Lib.CSharp.Enumerable.is_collection", [source]) { Type = IrPrim.Bool };
        return isNull ? new IrUnary(loc, UnOp.Not, test) { Type = IrPrim.Bool } : test;
    }

    /// <summary>R34.20. <c>c is null</c> / <c>c is not null</c> on a collection alias.</summary>
    private IrExpr? CollectionAliasPattern(IsPatternExpressionSyntax node, IrLoc loc) =>
        node.Pattern switch
        {
            ConstantPatternSyntax { Expression: var k } when Unparenthesized(k).IsKind(Microsoft.CodeAnalysis.CSharp.SyntaxKind.NullLiteralExpression) =>
                CollectionAliasNullTest(node.Expression, true, loc),
            UnaryPatternSyntax { Pattern: ConstantPatternSyntax { Expression: var k } } u
                when u.OperatorToken.IsKind(Microsoft.CodeAnalysis.CSharp.SyntaxKind.NotKeyword) &&
                     Unparenthesized(k).IsKind(Microsoft.CodeAnalysis.CSharp.SyntaxKind.NullLiteralExpression) =>
                CollectionAliasNullTest(node.Expression, false, loc),
            _ => null,
        };

    /// <summary>
    /// R34.3, R34.6. <c>c.Count</c> on an <c>ICollection&lt;T&gt;</c>, and <c>en.Current</c>
    /// on an enumerator in scope. Null when the member is neither.
    /// </summary>
    private IrExpr? EnumerableMember(MemberAccessExpressionSyntax node, ISymbol? symbol, IrLoc loc)
    {
        if (symbol is IPropertySymbol { Name: "Count", IsStatic: false } &&
            IsEnumerableArgument(node.Expression) &&
            known.MapType(model.GetTypeInfo(node.Expression).Type) is IrEnumerableType { Collection: true })
            return new IrEnumOp(loc, EnumOpKind.Count, Lower(node.Expression), []) { Type = IrPrim.Int };
        if (symbol is IPropertySymbol { Name: "Current", IsStatic: false } &&
            CursorOf(node.Expression) is ({ } name, { } source))
            return new IrEnumOp(loc, EnumOpKind.Current, source, [Cursor(loc, name)])
                { Type = ((IrEnumerableType)source.Type!).Element };
        return null;
    }

    /// <summary>
    /// R34.6. <c>en.MoveNext()</c> on an enumerator in scope. <c>GetEnumerator()</c> on an
    /// enumerable is translated only where a <c>using</c> declares the enumerator
    /// (StmtLowerer); anywhere else it is refused. Null when the call is neither.
    /// </summary>
    private IrExpr? EnumerableCall(InvocationExpressionSyntax node, IMethodSymbol method, IrLoc loc)
    {
        if (node.Expression is not MemberAccessExpressionSyntax access) return null;
        if (method is { Name: "MoveNext", IsStatic: false, Parameters.IsEmpty: true } &&
            CursorOf(access.Expression) is ({ } name, { } source))
            return new IrEnumOp(loc, EnumOpKind.MoveNext, source, [Cursor(loc, name)]) { Type = IrPrim.Bool };
        if (method is { Name: "GetEnumerator", IsStatic: false, Parameters.IsEmpty: true } &&
            IsEnumerableArgument(access.Expression))
        {
            diagnostics.Error("PALCS0860", loc,
                $"`{node}` outside a `using` declaration. An enumerator of an enumerable argument is " +
                "translated when a `using` declares it, as `using (IEnumerator<T> en = e.GetEnumerator())` " +
                "or `using IEnumerator<T> en = e.GetEnumerator();` (doc/translation.md R34.6).");
            return new IrLiteral(loc, null);
        }
        if (CursorOf(access.Expression) is not null && method.Name != "Dispose")
        {
            diagnostics.Error("PALCS0861", loc,
                $"`{node}` on an enumerator. Only `MoveNext()` and `Current` are translated " +
                "(doc/translation.md R34.6).");
            return new IrLiteral(loc, null);
        }
        return null;
    }

    /// <summary>
    /// R34.2. <c>e == null</c> on an enumerable argument is false: the caller lends a
    /// resource, which a null reference is not. <c>o == e</c>, for an object <c>o</c>, is
    /// false too: the enumerable is owned apart from every object the method holds.
    /// </summary>
    private IrExpr? EnumerableEquality(BinaryExpressionSyntax node, IrLoc loc)
    {
        if (node.Kind() is not (Microsoft.CodeAnalysis.CSharp.SyntaxKind.EqualsExpression
                or Microsoft.CodeAnalysis.CSharp.SyntaxKind.NotEqualsExpression)) return null;
        bool IsNull(ExpressionSyntax e) =>
            Unparenthesized(e).IsKind(Microsoft.CodeAnalysis.CSharp.SyntaxKind.NullLiteralExpression);
        bool eq = node.IsKind(Microsoft.CodeAnalysis.CSharp.SyntaxKind.EqualsExpression);
        if (IsNull(node.Right) && CollectionAliasNullTest(node.Left, eq, loc) is { } l) return l;
        if (IsNull(node.Left) && CollectionAliasNullTest(node.Right, eq, loc) is { } r) return r;
        bool IsEnum(ExpressionSyntax e) => IsEnumerableArgument(e);
        bool Other(ExpressionSyntax e) =>
            Unparenthesized(e).IsKind(Microsoft.CodeAnalysis.CSharp.SyntaxKind.NullLiteralExpression) ||
            Unparenthesized(e) is ThisExpressionSyntax;
        if (!(IsEnum(node.Left) && Other(node.Right) || IsEnum(node.Right) && Other(node.Left))) return null;
        return new IrLiteral(loc, node.IsKind(Microsoft.CodeAnalysis.CSharp.SyntaxKind.NotEqualsExpression))
            { Type = IrPrim.Bool };
    }
}
