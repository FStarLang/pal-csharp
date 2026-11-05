using Microsoft.CodeAnalysis;
using Pal.Compiler.Ir;

namespace Pal.Compiler.Frontend;

/// <summary>
/// §25. Comparers, as the sorted collections use them. An <c>IComparer&lt;T&gt;</c> (or a
/// <c>Comparer&lt;T&gt;</c>) is a value: R22.30's <c>Pulse.Lib.CSharp.Order.comparer t</c>,
/// whose <c>Compare</c> is a pure function of its arguments. The supporting proofs are in
/// <c>Pulse.Lib.CSharp.Sorted</c>.
/// </summary>
public static class Sorted
{
    public const string Module = "Pulse.Lib.CSharp.Sorted";
    public const string Order = "Pulse.Lib.CSharp.Order";
    public const string ComparerType = Order + ".comparer";

    /// <summary><c>System.Collections.Generic.IComparer&lt;T&gt;</c> or <c>Comparer&lt;T&gt;</c>.</summary>
    public static bool IsComparerSymbol(ITypeSymbol? type) =>
        type is INamedTypeSymbol { Name: "IComparer" or "Comparer", Arity: 1 } named &&
        named.ContainingNamespace?.ToDisplayString() == "System.Collections.Generic";

    /// <summary>R25.1. The comparer types, or null.</summary>
    public static IrType? MapType(INamedTypeSymbol type, Func<ITypeSymbol, IrType?> map) =>
        IsComparerSymbol(type) && map(type.TypeArguments[0]) is { } element
            ? new IrUserSpecType("Comparer", ComparerType, [element])
            : null;

    /// <summary>Whether a lowered type is R25.1's comparer.</summary>
    public static bool IsComparer(IrType? type) => type is IrUserSpecType { FStar: ComparerType };

    /// <summary>
    /// R25.4. The types whose null the model cannot see: a type parameter, and a comparer.
    /// Whether a value of one is null is <c>is_null</c>.
    /// </summary>
    public static bool HasOpaqueNull(IrType? type) => type is IrTypeParamType || IsComparer(type);

    public static IrExpr IsNull(IrLoc loc, IrExpr value) =>
        new IrSpecOp(loc, Module + ".is_null", [value]) { Type = IrPrim.Bool, MachineArgs = true };

    /// <summary>
    /// R25.5. The comparer a BCL search is given: one that may be null stands for
    /// <c>Comparer&lt;T&gt;.Default</c> when it is.
    /// </summary>
    public static IrExpr OrDefault(IrLoc loc, IrExpr comparer) =>
        new IrSpecOp(loc, Module + ".or_default", [comparer]) { Type = comparer.Type, MachineArgs = true };
}
