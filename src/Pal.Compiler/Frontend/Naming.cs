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
    public static string Of(ISymbol symbol)
    {
        // A constructor's C# name is `.ctor`, which is not an F* identifier. `_ctor` is,
        // and because the type qualifier already contributes a separating `_`, the
        // generated module reads `Func_Counter__ctor` — visibly not a method a user could
        // have declared, since C# forbids a method whose name matches its own type.
        var name = symbol is IMethodSymbol { MethodKind: MethodKind.Constructor } ? "_ctor" : symbol.Name;
        return symbol.ContainingType is { } type ? $"{type.Name}_{name}" : name;
    }
}
