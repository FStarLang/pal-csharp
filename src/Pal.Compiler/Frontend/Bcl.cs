using System.Collections.Immutable;
using Microsoft.CodeAnalysis;
using Pal.Compiler.Ir;

namespace Pal.Compiler.Frontend;

/// <summary>
/// R20.10. The few BCL types and members production code leans on that have a pure
/// model: each is a function in <c>Pulse.Lib.CSharp.Bcl</c>, and each use lowers to an
/// <see cref="IrSpecOp"/>, which is what a <c>[SpecOp]</c> the user had written would
/// lower to. The table is closed: a BCL member not named here is still R18.1's refusal.
/// </summary>
public static class Bcl
{
    public const string Module = "Pulse.Lib.CSharp.Bcl";

    private static string F(string name) => $"{Module}.{name}";

    /// <summary>The value types the table models, or null.</summary>
    public static IrType? MapType(INamedTypeSymbol type, Func<ITypeSymbol, IrType?> map)
    {
        if (InSource(type)) return null;
        switch (type.OriginalDefinition.ToDisplayString())
        {
            case "System.Guid":
                return new IrUserSpecType("Guid", F("guid"), []);
            case "System.Text.RegularExpressions.Regex":
                return new IrUserSpecType("Regex", F("regex"), []);
            case "System.Collections.Generic.HashSet<T>":
                return map(type.TypeArguments[0]) is { } element
                    ? new IrUserSpecType("HashSet", F("hash_set"), [element])
                    : null;
            default:
                return null;
        }
    }

    /// <summary>
    /// R24.5. A type whose source is in the compilation is the program's own, not the
    /// BCL's: verifying `HashSet&lt;T&gt;` itself must not see it as the opaque model.
    /// </summary>
    private static bool InSource(INamedTypeSymbol type) =>
        type.OriginalDefinition.Locations.Any(l => l.IsInSource);

    /// <summary><c>Guid.Empty</c>, the one static member read.</summary>
    public static IrExpr? Member(ISymbol? symbol, IrLoc loc) =>
        symbol is IFieldSymbol { IsStatic: true, Name: "Empty" } f &&
        f.ContainingType.ToDisplayString() == "System.Guid"
            ? new IrSpecOp(loc, F("guid_empty"), [])
            : null;

    /// <summary>Whether <paramref name="method"/> is one of the table's.</summary>
    public static bool Models(IMethodSymbol method) =>
        !(method.ContainingType is { } owner && InSource(owner)) &&
        (method.ContainingType?.OriginalDefinition.ToDisplayString(), method.Name) is
            ("string", "IsNullOrWhiteSpace") or ("string", "Equals") or
            ("System.Text.RegularExpressions.Regex", "IsMatch") or
            ("System.Collections.Generic.HashSet<T>", "Contains");

    /// <summary>
    /// A call into the table. <paramref name="receiver"/> is the lowered receiver of an
    /// instance call. Returns null when the method is not one the table models, and an
    /// explanation in <paramref name="refusal"/> when it is one of the table's methods
    /// called in a way the model does not cover.
    /// </summary>
    public static IrExpr? Call(
        IMethodSymbol method, IrExpr? receiver, ImmutableArray<IrExpr> args,
        ImmutableArray<object?> constants, IrLoc loc, out string? refusal)
    {
        refusal = null;
        var owner = method.ContainingType?.OriginalDefinition.ToDisplayString();
        switch (owner, method.Name, method.IsStatic, args.Length)
        {
            case ("string", "IsNullOrWhiteSpace", true, 1):
                return Op("is_null_or_white_space", args[0]);
            // Only the ordinal comparison is a function of the two strings alone; every
            // other one consults a culture, which is not modelled.
            case ("string", "Equals", true, 3):
                if (constants[2] is int c && c == (int)StringComparison.Ordinal)
                    return Op("string_equals_ordinal", args[0], args[1]);
                refusal = "`string.Equals` translates with `StringComparison.Ordinal` only: every " +
                          "other comparison consults a culture, which is not modelled.";
                return null;
            // `IsMatch(null)` throws, so the input must be shown non-null.
            case ("System.Text.RegularExpressions.Regex", "IsMatch", false, 1) when receiver is not null:
                return Op("is_match", receiver, NonNull(args[0]));
            case ("System.Collections.Generic.HashSet<T>", "Contains", false, 1) when receiver is not null:
                return Op("hash_set_contains", receiver, args[0]);
            default:
                return null;
        }

        IrExpr Op(string name, params IrExpr[] operands) =>
            new IrSpecOp(loc, F(name), [.. operands]) { MachineArgs = true };
    }

    /// <summary><c>new Regex(pattern, options)</c> with both constant.</summary>
    public static IrExpr? Construct(
        INamedTypeSymbol type, ImmutableArray<object?> constants, ImmutableArray<IrExpr> elements,
        bool collection, IrLoc loc)
    {
        switch (type.OriginalDefinition.ToDisplayString())
        {
            case "System.Text.RegularExpressions.Regex"
                when !collection && constants is [string pattern, var options] &&
                     options is null or int:
                return new IrSpecOp(loc, F("regex_create"),
                [
                    new IrLiteral(loc, pattern) { Type = new IrPrim(PrimKind.String) },
                    new IrLiteral(loc, options ?? 0) { Type = new IrPrim(PrimKind.Int) },
                ]) { MachineArgs = true };
            case "System.Text.RegularExpressions.Regex" when !collection && constants is [string only]:
                return new IrSpecOp(loc, F("regex_create"),
                [
                    new IrLiteral(loc, only) { Type = new IrPrim(PrimKind.String) },
                    new IrLiteral(loc, 0) { Type = new IrPrim(PrimKind.Int) },
                ]) { MachineArgs = true };
            // A collection initializer: the set of its elements.
            case "System.Collections.Generic.HashSet<T>" when collection:
            {
                IrExpr set = new IrSpecOp(loc, F("hash_set_empty"), []);
                for (var i = elements.Length - 1; i >= 0; i--)
                    set = new IrSpecOp(loc, F("hash_set_add"), [elements[i], set]) { MachineArgs = true };
                return set;
            }
            default:
                return null;
        }
    }

    /// <summary>A nullable argument to a member that throws on null: its value.</summary>
    private static IrExpr NonNull(IrExpr arg) =>
        arg.Type is IrOptionType o
            ? new IrOptionOp(arg.Loc, OptionOpKind.Value, arg) { Type = o.Inner }
            : arg;
}
