using Microsoft.CodeAnalysis;
using Pal.Compiler.Ir;

namespace Pal.Compiler.Frontend;

/// <summary>
/// R35.7. Type tests and casts of an <c>object</c> (R29.4's <c>obj</c>) against a type
/// parameter or a pair: <c>Pulse.Lib.CSharp.TypeTest</c>'s <c>is_a</c> and <c>unbox</c>.
/// </summary>
public static class TypeTests
{
    public const string Module = "Pulse.Lib.CSharp.TypeTest";

    /// <summary>
    /// The type an <c>object</c> may be tested against and cast to: a type parameter, or a
    /// pair of values (<c>KeyValuePair&lt;K, V&gt;</c>, R29.1). A machine integer is not one
    /// (its box is a value of a type the model does not relate to its mathematical image),
    /// nor is a class (whose object a box would have to own) or <c>object</c> itself.
    /// </summary>
    public static IrType? Target(WellKnown known, ITypeSymbol? type) =>
        type is null or { SpecialType: SpecialType.System_Object } ? null :
        known.MapType(type) is { } mapped &&
        (mapped is IrTypeParamType ||
         mapped is IrUserSpecType { FStar: WellKnown.TupleType } && !WellKnown.IsObj(mapped))
            ? mapped
            : null;

    public static IrExpr IsA(IrLoc loc, IrType target, IrExpr o) =>
        new IrSpecOp(loc, Module + ".is_a", [o]) { TypeArgs = [target], Type = IrPrim.Bool };

    public static IrExpr Unbox(IrLoc loc, IrType target, IrExpr o) =>
        new IrSpecOp(loc, Module + ".unbox", [o]) { TypeArgs = [target], Type = target };

    /// <summary>R35.12. <c>is_a T o ? unbox T o : d</c>, as one well-typed term.</summary>
    public static IrExpr UnboxOr(IrLoc loc, IrType target, IrExpr o, IrExpr d) =>
        new IrSpecOp(loc, Module + ".unbox_or", [o, d]) { TypeArgs = [target], Type = target };

    /// <summary>The null <c>object</c>.</summary>
    public static IrExpr Null(IrLoc loc, IrType obj) =>
        new IrSpecOp(loc, Module + ".null_obj", []) { Type = obj };
}
