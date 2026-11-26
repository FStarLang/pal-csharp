using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using Pal.Compiler.Ir;

namespace Pal.Compiler.Frontend;

public sealed partial class ExprLowerer
{
    internal readonly Dictionary<string, IrVar> NominalIterators = [];
    internal readonly Dictionary<string, IrVar> NominalIteratorSources = [];
    internal readonly Dictionary<string, INamedTypeSymbol> NominalIteratorTypes = [];

    private bool NominalIteratorSlot(string local, ISymbol member, string iface, string name) =>
        NominalIteratorTypes[local].AllInterfaces
            .FirstOrDefault(i => i.OriginalDefinition.ToDisplayString() == iface)?
            .GetMembers(name).Any(s => EnumerationProtocols.Same(
                NominalIteratorTypes[local].FindImplementationForInterfaceMember(s), member)) == true;

    private IrExpr? NominalIteratorMember(MemberAccessExpressionSyntax node, ISymbol? member, IrLoc loc)
    {
        if (Unparenthesized(node.Expression) is not IdentifierNameSyntax id ||
            !NominalIterators.TryGetValue(id.Identifier.ValueText, out var cursor) ||
            cursor.Type is not IrNominalIteratorType it)
            return null;
        if (SpecPosition && member is IPropertySymbol p && Declarations.Has(p, known.SpecAttribute))
        {
            var operation = p.Name == it.Protocol.Ready ? "ready"
                : p.Name == it.Protocol.Pending ? "remaining"
                : p.Name == it.Protocol.CurrentItems ? "current_items"
                : p.Name == it.Protocol.Valid ? "valid" : null;
            if (operation is not null)
                return new IrSpecOp(loc, "Pulse.Lib.CSharp.Capability.Iterator." + operation, [cursor]) {
                    Type = operation is "ready" or "valid" ? IrPrim.Bool : new IrSeqType(it.Element)
                };
        }
        if (!SpecPosition && member is IPropertySymbol { IsStatic: false } &&
            NominalIteratorSlot(id.Identifier.ValueText, member, "System.Collections.Generic.IEnumerator<T>", "Current"))
            return new IrEnumOp(loc, EnumOpKind.IteratorValue,
                NominalIteratorSources[id.Identifier.ValueText], [cursor]) { Type = it.Element };
        diagnostics.Error("PALCS0866", loc, "Only checked protocol observations and Current are available on a nominal iterator.");
        return new IrLiteral(loc, null);
    }

    internal IrExpr? NominalIteratorCall(InvocationExpressionSyntax node, IMethodSymbol method, IrLoc loc)
    {
        if (node.Expression is not MemberAccessExpressionSyntax { Expression: IdentifierNameSyntax id } ||
            !NominalIterators.TryGetValue(id.Identifier.ValueText, out var cursor) ||
            cursor.Type is not IrNominalIteratorType it)
            return null;
        if (!method.IsStatic && method.Parameters.IsEmpty &&
            (NominalIteratorSlot(id.Identifier.ValueText, method, "System.Collections.IEnumerator", "MoveNext") ||
             NominalIteratorSlot(id.Identifier.ValueText, method, "System.IDisposable", "Dispose")))
            return new IrEnumOp(loc, method.Name == "MoveNext"
                ? EnumOpKind.IteratorNext : EnumOpKind.IteratorDispose,
                NominalIteratorSources[id.Identifier.ValueText], [cursor]) {
                    Type = method.Name == "MoveNext" ? IrPrim.Bool : IrPrim.Void
                };
        diagnostics.Error("PALCS0866", loc, "Only checked MoveNext and Dispose calls are available on a nominal iterator.");
        return new IrLiteral(loc, null);
    }
}
