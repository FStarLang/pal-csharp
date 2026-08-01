using Microsoft.CodeAnalysis;

namespace Pal.Compiler.Frontend;

/// <summary>
/// The stable name a C# member carries through the IR and into the generated
/// Pulse (doc/translation.md R2.2).
/// </summary>
/// <remarks>
/// PAL can use a C function's own name, because C has one global function
/// namespace. C# does not: two classes in the same program may each declare
/// `Abs`, and each would want the module `Func_Abs`. Qualifying by the declaring
/// type is the smallest rule that keeps the mapping injective, and it is applied
/// uniformly rather than only on collision, so a program's generated module names
/// do not change when an unrelated class is added.
/// </remarks>
public static class Naming
{
    public static string Of(ISymbol symbol) =>
        symbol.ContainingType is { } type ? $"{type.Name}_{symbol.Name}" : symbol.Name;
}
