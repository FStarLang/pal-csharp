using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using Pal.Compiler.Ir;

namespace Pal.Compiler.Frontend;

/// <summary>R30.29. References read once, as <c>option</c>s (<see cref="RefSnapshots"/>).</summary>
public sealed partial class ExprLowerer
{
    /// <summary>R30.29. The <c>option</c> local each snapshot <c>ref</c> local is.</summary>
    private readonly Dictionary<ISymbol, IrVar> _snapshots = new(SymbolEqualityComparer.Default);

    /// <summary>
    /// R30.29. In the contract of a snapshot method, the type of the <c>option</c> it
    /// returns: <c>Result</c> is the value it refers to, and <c>Unsafe.IsNullRef(ref Result)</c>
    /// whether it is null.
    /// </summary>
    public IrOptionType? SnapshotResult { get; init; }

    /// <summary>
    /// R30.30. The type of the value the method a clause specifies returns; the shim's
    /// <c>Result</c> parameter is nullable-oblivious, so its own type does not say.
    /// </summary>
    public IrType? DeclaredResult { get; init; }

    /// <summary>R30.29. Set while lowering a snapshot call for its <c>option</c>.</summary>
    private bool _snapshotRaw;

    /// <summary>R30.29. Makes the <c>ref</c> local <paramref name="symbol"/> the <c>option</c> local <paramref name="raw"/>.</summary>
    public void Snapshot(ISymbol symbol, IrVar raw)
    {
        _snapshots[symbol] = raw;
        Alias(symbol, Deref(raw));
    }

    public bool IsSnapshot(ISymbol symbol) => _snapshots.ContainsKey(symbol);

    private static IrExpr Deref(IrExpr raw) =>
        new IrOptionOp(raw.Loc, OptionOpKind.Value, raw) { Type = (raw.Type as IrOptionType)?.Inner };

    /// <summary>R30.29. The <c>option</c> type a snapshot method returns, or the result type of a method.</summary>
    public IrOptionType? SnapshotType(IMethodSymbol method) =>
        RefSnapshots.IsSnapshot(method, model.Compilation) && known.MapType(method.ReturnType) is { } t
            ? new IrOptionType(t) : null;

    private IrOptionType? EnclosingSnapshot(SyntaxNode node) =>
        SnapshotResult ?? (RefSnapshots.Enclosing(node, model) is { } m ? SnapshotType(m) : null);

    /// <summary>
    /// R30.29. The <c>option</c> a reference denotes, where <paramref name="e"/> is one read
    /// as a reference: a snapshot local, a call of a snapshot method, a null reference, or the
    /// result of the snapshot method being specified. Null for any other expression.
    /// </summary>
    public IrExpr? LowerRaw(ExpressionSyntax e, IrOptionType? nullType = null)
    {
        while (true)
        {
            if (e is ParenthesizedExpressionSyntax p) e = p.Expression;
            else if (e is PostfixUnaryExpressionSyntax { RawKind: (int)SyntaxKind.SuppressNullableWarningExpression } sn) e = sn.Operand;
            else break;
        }
        var loc = Locations.From(e);
        var symbol = model.GetSymbolInfo(e).Symbol;
        if (e is IdentifierNameSyntax && symbol is not null && _snapshots.TryGetValue(symbol, out var raw))
            return raw;
        if (e is IdentifierNameSyntax && symbol is IParameterSymbol { Name: SpecBinder.ResultParameter } rp &&
            rp.ContainingSymbol.Name.StartsWith(SpecBinder.ShimMethodPrefix, StringComparison.Ordinal) &&
            SnapshotResult is { } resultType)
            return new IrResult(loc) { Type = resultType };
        if (e is not InvocationExpressionSyntax call || symbol is not IMethodSymbol method) return null;
        if (RefSnapshots.IsNullRef(call, model))
        {
            var t = nullType ?? (known.MapType(method.ReturnType) is { } inner ? new IrOptionType(inner) : null);
            return t is null ? null : new IrNull(loc) { Type = t };
        }
        if (known.IsPalIntrinsic(method) && method.Name is nameof(PalLang.Pal.ResultRef) &&
            EnclosingSnapshot(call) is { } enclosing)
            return InLoop(call)
                ? new IrVar(loc, StmtLowerer.ReturnedValue) { Type = enclosing }
                : new IrResult(loc) { Type = enclosing };
        if (SnapshotType(method) is null) return null;
        var outer = _snapshotRaw;
        _snapshotRaw = true;
        try { return LowerInvocation(call, loc); }
        finally { _snapshotRaw = outer; }
    }

    /// <summary>R30.29. <c>Unsafe.IsNullRef(ref r)</c>: whether the snapshot is <c>None</c>.</summary>
    private IrExpr? LowerIsNullRef(InvocationExpressionSyntax node, IMethodSymbol method, IrLoc loc)
    {
        if (!RefSnapshots.IsIsNullRef(method) || node.ArgumentList.Arguments is not [var arg]) return null;
        if (LowerRaw(arg.Expression) is not { } raw)
            return Refused("PALCS0751", loc,
                $"`{node}` tests a reference that is not one R30.29 reads as an `option`: a `ref` local " +
                "bound by a lookup that may return `Unsafe.NullRef`, or such a call (doc/translation.md R30.29).");
        return new IrUnary(loc, UnOp.Not, new IrOptionOp(loc, OptionOpKind.HasValue, raw) { Type = IrPrim.Bool })
            { Type = IrPrim.Bool };
    }
}
