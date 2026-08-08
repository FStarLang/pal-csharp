using System.Linq;
using System.Text;
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
        // R9.20c. A getter's C# name is `get_P`, a name the user did not write and C#
        // will not let them write. The declaration is the property, so the module is
        // `Func_C_P` — injective, because C# forbids a property and a method of one name
        // in one type.
        var name = Mangle(symbol);
        var qualified = symbol.ContainingType is { } type ? $"{type.Name}_{name}" : name;
        return qualified + Overload(symbol, name);
    }

    /// <summary>
    /// R2.1a. The suffix that separates one member of an overload set from the others, and
    /// the empty string when the member is not overloaded. It is keyed on the *mangled*
    /// name rather than the C# one, so a property and a method that would collide after
    /// R9.20c are separated here too.
    /// </summary>
    private static string Overload(ISymbol symbol, string name)
    {
        if (symbol is not IMethodSymbol method || symbol.ContainingType is not { } type)
            return "";

        // Against the *definitions*, both sides. A call to `Exchange<int>` presents a
        // constructed symbol which is not `Equals` to the `Exchange<T>` sitting in
        // `GetMembers`, so comparing it directly made every generic method an overload of
        // itself -- and R15.1 is explicit that a generic method emits one module for all
        // its instantiations, so the suffix would have named a module nothing generates.
        var definition = method.OriginalDefinition;
        var overloaded = type.OriginalDefinition.GetMembers()
            .Any(m => m is IMethodSymbol other
                      && !SymbolEqualityComparer.Default.Equals(other.OriginalDefinition, definition)
                      && Mangle(other) == name);
        if (!overloaded) return "";

        if (definition.Parameters.Length == 0) return "_unit";
        return "_" + string.Join("_", definition.Parameters.Select(p => Token(p.Type)));
    }

    /// <summary>The unqualified part of <see cref="Of"/>, which is what an overload set shares.</summary>
    private static string Mangle(ISymbol symbol) => symbol switch
    {
        IMethodSymbol { MethodKind: MethodKind.Constructor } => "_ctor",
        IMethodSymbol { MethodKind: MethodKind.PropertyGet, AssociatedSymbol: { } p } => p.Name,
        _ => symbol.Name,
    };

    /// <summary>
    /// R2.1a. A type's C# spelling with every non-identifier character replaced by `_`, so
    /// the token is derived from what the author wrote rather than from a scheme of the
    /// compiler's own. Two distinct types can in principle reach one token; PALCS0501
    /// reports that rather than the emitter working around it.
    /// </summary>
    private static string Token(ITypeSymbol type)
    {
        var text = type.ToDisplayString(SymbolDisplayFormat.MinimallyQualifiedFormat);
        var sb = new StringBuilder(text.Length);
        foreach (var c in text) sb.Append(char.IsLetterOrDigit(c) || c == '_' ? c : '_');
        return sb.ToString();
    }
}
