using System.Collections.Immutable;
using System.Runtime.CompilerServices;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using Pal.Compiler.Diagnostics;

namespace Pal.Compiler.Frontend;

/// <summary>
/// R27.57. A <em>representation-sharing</em> subclass: a <c>sealed</c> class deriving from
/// a class verified at its exact type (R27.1), declaring no state and no model of its own.
/// Its objects are records of the base's representation under the base's invariant, so it
/// is translated as the base's type; what differs is only which body a virtual call reaches,
/// and that is decided statically, because translated code never lets one of its objects be
/// seen at any other static type (<see cref="Check"/>).
/// </summary>
internal static class Subclasses
{
    /// <summary>The base <paramref name="type"/> shares its representation with, or null.</summary>
    public static INamedTypeSymbol? AliasBase(ITypeSymbol? type, WellKnown known)
    {
        if (type is not INamedTypeSymbol { TypeKind: TypeKind.Class, IsSealed: true, IsAbstract: false, IsStatic: false } s)
            return null;
        var d = s.OriginalDefinition;
        if (d.BaseType is not { SpecialType: not SpecialType.System_Object } b ||
            b.OriginalDefinition is { IsSealed: true } or { IsAbstract: true } ||
            !b.OriginalDefinition.GetMembers().Any(m => Declarations.Has(m, known.ModelAttribute)))
            return null;
        if (Declarations.Has(d, known.RegionAttribute) || Declarations.Has(d, known.PlainAttribute) ||
            Declarations.Has(d, known.InvariantAttribute))
            return null;
        if (d.GetMembers().Any(m => m is IFieldSymbol { IsStatic: false, IsConst: false } ||
                                    Declarations.Has(m, known.ModelAttribute) ||
                                    Declarations.Has(m, known.InvariantAttribute)))
            return null;
        // Under `[TranslateAnnotatedOnly]` a subclass nothing annotates is not translated at
        // all (R27.1), and is no alias of anything.
        if (known.AnnotatedOnly && !Declarations.IsAnnotated(d, known) &&
            !d.GetMembers().Any(m => Declarations.IsAnnotated(m, known) ||
                                     m is IMethodSymbol { AssociatedSymbol: { } a } && Declarations.IsAnnotated(a, known)))
            return null;
        return s.BaseType;
    }

    public static bool IsAlias(ITypeSymbol? type, WellKnown known) => AliasBase(type, known) is not null;

    /// <summary>The base members <paramref name="s"/> overrides, at every level of the chain.</summary>
    public static ImmutableHashSet<IMethodSymbol> Overridden(INamedTypeSymbol s)
    {
        var result = ImmutableHashSet.CreateBuilder<IMethodSymbol>(SymbolEqualityComparer.Default);
        foreach (var m in s.OriginalDefinition.GetMembers())
        {
            IEnumerable<IMethodSymbol> methods = m switch
            {
                IMethodSymbol { IsOverride: true } om => [om],
                IPropertySymbol { IsOverride: true } p => new[] { p.GetMethod, p.SetMethod }.OfType<IMethodSymbol>(),
                _ => [],
            };
            foreach (var om in methods)
                for (var at = om.OverriddenMethod; at is not null; at = at.OverriddenMethod)
                    result.Add(at.OriginalDefinition);
        }
        return result.ToImmutable();
    }

    /// <summary>The member of <paramref name="s"/> that overrides <paramref name="m"/>, if any.</summary>
    public static IMethodSymbol? OverrideOf(INamedTypeSymbol s, IMethodSymbol m)
    {
        var target = m.OriginalDefinition;
        foreach (var member in s.OriginalDefinition.GetMembers())
        {
            IEnumerable<IMethodSymbol> methods = member switch
            {
                IMethodSymbol { IsOverride: true } om => [om],
                IPropertySymbol { IsOverride: true } p => new[] { p.GetMethod, p.SetMethod }.OfType<IMethodSymbol>(),
                _ => [],
            };
            foreach (var om in methods)
                for (var at = om.OverriddenMethod; at is not null; at = at.OverriddenMethod)
                    if (SymbolEqualityComparer.Default.Equals(at.OriginalDefinition, target))
                        return om;
        }
        return null;
    }

    private static readonly ConditionalWeakTable<Compilation, Dictionary<IMethodSymbol, ImmutableHashSet<IMethodSymbol>>> Memo = new();

    /// <summary>
    /// Every member a call of <paramref name="m"/> can call, at any receiver: the methods,
    /// constructors and accessors its body names, transitively through those with source.
    /// </summary>
    public static ImmutableHashSet<IMethodSymbol> Closure(IMethodSymbol m, Compilation compilation)
    {
        var memo = Memo.GetOrCreateValue(compilation);
        var root = m.OriginalDefinition;
        if (memo.TryGetValue(root, out var known)) return known;
        // The root is in its own closure only when it is called again.
        var seen = new HashSet<IMethodSymbol>(SymbolEqualityComparer.Default);
        var work = new Stack<IMethodSymbol>();
        foreach (var callee in Callees(root, compilation))
            if (seen.Add(callee)) work.Push(callee);
        while (work.Count > 0)
        {
            var at = work.Pop();
            foreach (var callee in Callees(at, compilation))
                if (seen.Add(callee)) work.Push(callee);
        }
        var result = seen.ToImmutableHashSet<IMethodSymbol>(SymbolEqualityComparer.Default);
        memo[root] = result;
        return result;
    }

    private static IEnumerable<IMethodSymbol> Callees(IMethodSymbol m, Compilation compilation)
    {
        IEnumerable<SyntaxReference> refs = m.DeclaringSyntaxReferences;
        if (m.AssociatedSymbol is { } a) refs = refs.Concat(a.DeclaringSyntaxReferences);
        foreach (var r in refs)
        {
            if (!compilation.ContainsSyntaxTree(r.SyntaxTree)) continue;
            var model = compilation.GetSemanticModel(r.SyntaxTree);
            foreach (var node in r.GetSyntax().DescendantNodesAndSelf())
            {
                foreach (var s in Named(node, model))
                    yield return s.OriginalDefinition;
            }
        }
    }

    /// <summary>The members <paramref name="node"/> itself names or runs.</summary>
    private static IEnumerable<IMethodSymbol> Named(SyntaxNode node, SemanticModel model)
    {
        switch (node)
        {
            case ForEachStatementSyntax fe:
                var info = model.GetForEachStatementInfo(fe);
                if (info.GetEnumeratorMethod is { } ge) yield return ge;
                if (info.MoveNextMethod is { } mn) yield return mn;
                if (info.CurrentProperty?.GetMethod is { } cur) yield return cur;
                if (info.DisposeMethod is { } dm) yield return dm;
                yield break;
            case InvocationExpressionSyntax or BaseObjectCreationExpressionSyntax or ConstructorInitializerSyntax
                 or IdentifierNameSyntax or GenericNameSyntax or ElementAccessExpressionSyntax
                 or ElementBindingExpressionSyntax:
                var sym = model.GetSymbolInfo(node).Symbol;
                if (sym is IMethodSymbol ms) yield return ms;
                else if (sym is IPropertySymbol p)
                {
                    if (p.GetMethod is { } g) yield return g;
                    if (p.SetMethod is { } st) yield return st;
                }
                yield break;
        }
    }

    /// <summary>Whether a call of <paramref name="m"/> on an object of <paramref name="s"/> can reach a body <paramref name="s"/> overrides.</summary>
    public static bool Reaches(IMethodSymbol m, INamedTypeSymbol s, Compilation compilation)
    {
        var overridden = Overridden(s);
        return Closure(m, compilation).Any(overridden.Contains);
    }

    /// <summary>The name of the replica of <paramref name="m"/> verified at <paramref name="s"/>.</summary>
    public static string ReplicaName(IMethodSymbol m, INamedTypeSymbol s)
    {
        var full = Naming.Of(m);
        var prefix = m.ContainingType.Name + "_";
        return s.Name + "_" + (full.StartsWith(prefix, StringComparison.Ordinal) ? full[prefix.Length..] : full);
    }

    /// <summary>
    /// R27.57. The module a call of the instance member <paramref name="method"/> runs, when
    /// its receiver is an object of the representation-sharing subclass <paramref name="s"/>
    /// (<paramref name="viaBase"/> for <c>base.M()</c>, which C# does not dispatch). An
    /// override is called directly; a base body that can reach an override is verified
    /// again at <paramref name="s"/> as a replica, whose own calls on <c>this</c> bind the
    /// same way; any other base body is the base's, which runs exactly as verified.
    /// </summary>
    public static string Bind(IMethodSymbol method, INamedTypeSymbol s, bool viaBase, WellKnown known, Compilation compilation)
    {
        if (SymbolEqualityComparer.Default.Equals(method.ContainingType?.OriginalDefinition, s.OriginalDefinition))
            return Naming.Of(method);
        if (!viaBase && OverrideOf(s, method) is { } o) return Naming.Of(o);
        if (!Reaches(method, s, compilation)) return Naming.Of(method);
        var name = ReplicaName(method, s);
        if (known.ReplicaSeen.Add(name))
            known.ReplicaDemand.Enqueue(new WellKnown.ReplicaRequest(Naming.Of(method), s, name));
        return name;
    }

    /// <summary>
    /// R27.57. The receiver class a call runs at, when it is a representation-sharing
    /// subclass: the static type of an explicit receiver, or, for <c>this</c> and
    /// <c>base</c>, the class whose body is being lowered (a replica's class while one is).
    /// </summary>
    public static INamedTypeSymbol? ReceiverClass(ExpressionSyntax? receiver, SyntaxNode at, SemanticModel model, WellKnown known)
    {
        if (receiver is null or ThisExpressionSyntax or BaseExpressionSyntax)
        {
            if (known.Replica is { } r) return r.At;
            var self = model.GetEnclosingSymbol(at.SpanStart)?.ContainingType;
            return IsAlias(self, known) ? self : null;
        }
        var t = model.GetTypeInfo(receiver).Type as INamedTypeSymbol;
        return IsAlias(t, known) ? t : null;
    }

    /// <summary>
    /// R27.57. What keeps every object of a representation-sharing subclass <c>S</c> at
    /// static type <c>S</c>: no conversion of an <c>S</c> value to another type, and, in a
    /// body that runs with an <c>S</c> as <c>this</c>, no use of <c>this</c> as a value
    /// other than as the argument of a constructor of a class none of whose members can
    /// reach an override of <c>S</c>. Members of <c>S</c> reached through a property are
    /// refused when they would need a replica.
    /// </summary>
    public static void Check(IEnumerable<(SyntaxNode Body, IMethodSymbol Symbol)> translated,
        Compilation compilation, WellKnown known, DiagnosticBag diagnostics)
    {
        var atS = new Dictionary<IMethodSymbol, INamedTypeSymbol>(SymbolEqualityComparer.Default);
        var work = new Stack<(IMethodSymbol, INamedTypeSymbol)>();
        void Runs(IMethodSymbol m, INamedTypeSymbol s)
        {
            if (atS.ContainsKey(m.OriginalDefinition)) return;
            atS[m.OriginalDefinition] = s.OriginalDefinition;
            work.Push((m.OriginalDefinition, s.OriginalDefinition));
        }

        foreach (var (body, symbol) in translated)
        {
            if (!compilation.ContainsSyntaxTree(body.SyntaxTree)) continue;
            var model = compilation.GetSemanticModel(body.SyntaxTree);
            if (IsAlias(symbol.ContainingType, known) && !symbol.IsStatic)
                Runs(symbol, symbol.ContainingType);
            foreach (var node in body.DescendantNodesAndSelf())
            {
                // A conversion of an object of `S` to another type.
                if (node is ExpressionSyntax e && model.GetTypeInfo(e) is { Type: { } from, ConvertedType: { } to } &&
                    IsAlias(from, known) && !SymbolEqualityComparer.Default.Equals(from.OriginalDefinition, to.OriginalDefinition) &&
                    to.TypeKind != TypeKind.Error)
                    diagnostics.Error("PALCS0715", Locations.From(node),
                        $"An object of `{from.Name}` used as a `{to.Name}`. `{from.Name}` shares its base's " +
                        "representation and is verified only where its exact class is known statically " +
                        "(doc/translation.md R27.57).");
                if (node is CastExpressionSyntax or BinaryExpressionSyntax { RawKind: (int)SyntaxKind.AsExpression } &&
                    (node switch
                    {
                        CastExpressionSyntax ce => ce.Expression,
                        BinaryExpressionSyntax be => be.Left,
                        _ => null,
                    }) is { } operand &&
                    model.GetTypeInfo(operand).Type is { } castFrom && IsAlias(castFrom, known) &&
                    !SymbolEqualityComparer.Default.Equals(castFrom.OriginalDefinition, model.GetTypeInfo(node).Type?.OriginalDefinition))
                    diagnostics.Error("PALCS0715", Locations.From(node),
                        $"An object of `{castFrom.Name}` cast or tested at another type. `{castFrom.Name}` shares its " +
                        "base's representation and is verified only where its exact class is known statically " +
                        "(doc/translation.md R27.57).");
                if (node is MemberAccessExpressionSyntax ma && !IsInvoked(ma) &&
                    model.GetSymbolInfo(ma).Symbol is IPropertySymbol prop &&
                    IsAlias(model.GetTypeInfo(ma.Expression).Type, known) is true &&
                    model.GetTypeInfo(ma.Expression).Type is INamedTypeSymbol ps &&
                    new[] { prop.GetMethod, prop.SetMethod }.OfType<IMethodSymbol>()
                        .Any(a => OverrideOf(ps, a) is not null || Reaches(a, ps, compilation)))
                    diagnostics.Error("PALCS0715", Locations.From(node),
                        $"The property `{prop.Name}` of `{ps.Name}` reaches a member `{ps.Name}` overrides. " +
                        "A replica is made for a method, not a property (doc/translation.md R27.57).");
                if (node is InvocationExpressionSyntax inv && model.GetSymbolInfo(inv).Symbol is IMethodSymbol { IsStatic: false } callee &&
                    ReceiverOf(inv) is var recv && recv is not ThisExpressionSyntax and not BaseExpressionSyntax and not null &&
                    model.GetTypeInfo(recv).Type is INamedTypeSymbol rs && IsAlias(rs, known) &&
                    !SymbolEqualityComparer.Default.Equals(callee.ContainingType.OriginalDefinition, rs.OriginalDefinition) &&
                    OverrideOf(rs, callee) is null)
                    Runs(callee, rs);
            }
        }

        while (work.Count > 0)
        {
            var (m, s) = work.Pop();
            foreach (var r in m.DeclaringSyntaxReferences.Concat(m.AssociatedSymbol?.DeclaringSyntaxReferences ?? []))
            {
                if (!compilation.ContainsSyntaxTree(r.SyntaxTree)) continue;
                var model = compilation.GetSemanticModel(r.SyntaxTree);
                foreach (var node in r.GetSyntax().DescendantNodesAndSelf())
                {
                    if (node is InvocationExpressionSyntax inv && model.GetSymbolInfo(inv).Symbol is IMethodSymbol { IsStatic: false } c &&
                        ReceiverOf(inv) is null or ThisExpressionSyntax or BaseExpressionSyntax &&
                        OverrideOf(s, c) is null &&
                        !SymbolEqualityComparer.Default.Equals(c.ContainingType.OriginalDefinition, s))
                        Runs(c, s);
                    if (node is ThisExpressionSyntax th && EscapesThis(th, model, s, compilation) is { } why)
                        diagnostics.Error("PALCS0715", Locations.From(node),
                            $"`this` {why} in `{m.Name}`, which runs with an object of `{s.Name}` as `this`. " +
                            $"`{s.Name}` shares its base's representation, and an object of it seen at another " +
                            "static type would reach base bodies its overrides replace (doc/translation.md R27.57).");
                }
            }
        }
    }

    private static bool IsInvoked(MemberAccessExpressionSyntax ma) =>
        ma.Parent is InvocationExpressionSyntax inv && inv.Expression == ma;

    private static ExpressionSyntax? ReceiverOf(InvocationExpressionSyntax inv) => inv.Expression switch
    {
        MemberAccessExpressionSyntax ma => ma.Expression,
        MemberBindingExpressionSyntax => inv.FirstAncestorOrSelf<ConditionalAccessExpressionSyntax>()?.Expression,
        _ => null,
    };

    /// <summary>Why a use of <c>this</c> lets an object of <paramref name="s"/> escape, or null.</summary>
    private static string? EscapesThis(ThisExpressionSyntax th, SemanticModel model, INamedTypeSymbol s, Compilation compilation)
    {
        SyntaxNode at = th;
        while (at.Parent is ParenthesizedExpressionSyntax) at = at.Parent;
        switch (at.Parent)
        {
            case MemberAccessExpressionSyntax ma when ma.Expression == at: return null;
            case ElementAccessExpressionSyntax ea when ea.Expression == at: return null;
            case ConditionalAccessExpressionSyntax ca when ca.Expression == at: return null;
            case BinaryExpressionSyntax b when b.IsKind(SyntaxKind.EqualsExpression) || b.IsKind(SyntaxKind.NotEqualsExpression):
                return null;
            case ArgumentSyntax { Parent: ArgumentListSyntax { Parent: var call } }:
                if (call is InvocationExpressionSyntax refEq &&
                    model.GetSymbolInfo(refEq).Symbol is IMethodSymbol { Name: "ReferenceEquals", ContainingType.SpecialType: SpecialType.System_Object })
                    return null;
                if (call is BaseObjectCreationExpressionSyntax &&
                    model.GetSymbolInfo(call).Symbol is IMethodSymbol { ContainingType: { } made } &&
                    !InHierarchy(made, s) &&
                    made.OriginalDefinition.GetMembers().OfType<IMethodSymbol>().All(x => !Reaches(x, s, compilation)))
                    return null;
                return "is passed as an argument";
            default:
                return "is used as a value";
        }
    }

    private static bool InHierarchy(INamedTypeSymbol t, INamedTypeSymbol s)
    {
        for (var at = (INamedTypeSymbol?)s; at is not null; at = at.BaseType)
            if (SymbolEqualityComparer.Default.Equals(at.OriginalDefinition, t.OriginalDefinition)) return true;
        return false;
    }
}
