using System.Collections.Immutable;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using Pal.Compiler.Diagnostics;
using Pal.Compiler.Ir;

namespace Pal.Compiler.Frontend;

/// <summary>Logical fields are properties in C#, but never getter calls in the IR.</summary>
internal static class GhostStorage
{
    public static bool Is(ISymbol? symbol, WellKnown known) =>
        symbol is IPropertySymbol && Declarations.Has(symbol, known.GhostFieldAttribute);

    public static string Key(ISymbol property) => $"{property.ContainingType.Name}_ghost_initial_{property.Name}";

    // Validate before lowering: normalization can discard an unused read or a ref alias,
    // but the CLR would still evaluate its throwing getter.
    public static void Validate(Compilation compilation, WellKnown known, DiagnosticBag diagnostics)
    {
        foreach (var tree in compilation.SyntaxTrees)
        {
            var model = compilation.Model(tree);
            foreach (var node in tree.GetRoot().DescendantNodes())
            {
                if (node is BasePropertyDeclarationSyntax declaration &&
                    model.GetDeclaredSymbol(declaration) is IPropertySymbol property && Is(property, known))
                {
                    var syntax = declaration as PropertyDeclarationSyntax;
                    var getter = syntax?.AccessorList?.Accessors.FirstOrDefault(a =>
                        a.Keyword.ValueText == "get");
                    var expression = syntax?.ExpressionBody?.Expression ?? getter?.ExpressionBody?.Expression;
                    var thrown = expression is ThrowExpressionSyntax t ? t.Expression
                        : getter?.Body?.Statements is [ThrowStatementSyntax s] ? s.Expression : null;
                    var stub = thrown is ObjectCreationExpressionSyntax creation &&
                        model.GetTypeInfo(creation).Type?.ToDisplayString() == "System.InvalidOperationException" &&
                        creation.Initializer is null &&
                        (creation.ArgumentList is null || creation.ArgumentList.Arguments.All(a =>
                            model.GetConstantValue(a.Expression).HasValue));
                    if (property is not { IsStatic: false, IsIndexer: false, IsVirtual: false,
                            IsAbstract: false, IsOverride: false, ReturnsByRef: true,
                            ReturnsByRefReadonly: false, SetMethod: null, GetMethod: not null,
                            ContainingType.TypeKind: TypeKind.Class } ||
                        !property.ExplicitInterfaceImplementations.IsEmpty ||
                        property.ContainingType.AllInterfaces.Any(i => i.GetMembers().Any(m =>
                            SymbolEqualityComparer.Default.Equals(
                                property.ContainingType.FindImplementationForInterfaceMember(m), property))) ||
                        !(known.HasModel(property.ContainingType) || known.IsPlainLike(property.ContainingType)) ||
                        Borrowing.IsBorrowingClass(property.ContainingType, known) ||
                        Declarations.Has(property, known.SpecAttribute) ||
                        Declarations.Has(property, known.ModelAttribute) ||
                        Declarations.Has(property, known.LemmaAttribute) ||
                        Declarations.Has(property, known.SpecOpAttribute) ||
                        Declarations.Has(property, known.PulseBodyAttribute) ||
                        Declarations.Has(property, known.AdmitAttribute) ||
                        syntax?.Initializer is not null || !stub ||
                        known.MapType(property.Type) is not IrUserSpecType ||
                        string.IsNullOrWhiteSpace(Declarations.StringArgument(
                            Declarations.Find(property, known.GhostFieldAttribute)!)))
                        diagnostics.Error("PALCS0770", Locations.From(declaration),
                            "[GhostField] requires a nonvirtual instance ref (not ref readonly) throwing property " +
                            "in a translated class, an erased specification type, and a pure initializer. " +
                            "Interfaces, indexers, setters, backing storage and other member classifications are not supported.");
                }

                if (node is not IdentifierNameSyntax name ||
                    !Is(model.GetSymbolInfo(name).Symbol, known)) continue;
                // A qualified name is checked as a whole, once.
                ExpressionSyntax access = name.Parent is MemberAccessExpressionSyntax member && member.Name == name
                    ? member : name;
                if (access.Ancestors().OfType<AttributeSyntax>().Any()) continue;
                if (access.Ancestors().OfType<InvocationExpressionSyntax>().Any(i =>
                    i.Expression is IdentifierNameSyntax { Identifier.ValueText: "nameof" })) continue;

                var enclosing = model.GetEnclosingSymbol(access.SpanStart);
                if (enclosing is IMethodSymbol { AssociatedSymbol: { } associated }) enclosing = associated;
                var specBody = enclosing is not null &&
                    (Declarations.Has(enclosing, known.ModelAttribute) ||
                     Declarations.Has(enclosing, known.SpecAttribute) ||
                     Declarations.Has(enclosing, known.LemmaAttribute));
                var erasedCall = access.Ancestors().OfType<InvocationExpressionSyntax>().Any(i =>
                    model.GetSymbolInfo(i).Symbol is IMethodSymbol m &&
                    (known.IsPalIntrinsic(m) || Declarations.Has(m, known.LemmaAttribute) ||
                     Declarations.Has(m, known.SpecOpAttribute)) &&
                    m.GetAttributes().Any(a => a.AttributeClass?.ToDisplayString() ==
                        "System.Diagnostics.ConditionalAttribute" && Declarations.StringArgument(a) == "PAL"));
                // A reference may be used only as the direct destination of UpdateGhost.
                var refUse = access.Ancestors().FirstOrDefault(a =>
                    a is ArgumentSyntax or RefExpressionSyntax or AssignmentExpressionSyntax);
                var writes = refUse is RefExpressionSyntax or AssignmentExpressionSyntax ||
                    refUse is ArgumentSyntax arg && arg.RefKindKeyword.RawKind != 0;
                var updateTarget = access.Parent is ArgumentSyntax destination &&
                    destination.Parent is ArgumentListSyntax arguments &&
                    arguments.Arguments.IndexOf(destination) == 0 &&
                    arguments.Parent is InvocationExpressionSyntax update &&
                    model.GetSymbolInfo(update).Symbol is IMethodSymbol intrinsic &&
                    known.IsPalIntrinsic(intrinsic) && intrinsic.Name == nameof(PalLang.Pal.UpdateGhost);
                if ((!specBody && !erasedCall) || (writes && !updateTarget))
                    diagnostics.Error("PALCS0771", Locations.From(access),
                        "A [GhostField] has no runtime storage: read it only in erased proof/specification " +
                        "contexts and write it only as the direct destination of Pal.UpdateGhost; references cannot escape.");
            }
        }
    }

    public static void ValidateCollected(Compilation compilation, WellKnown known,
        IEnumerable<ISymbol> fields, DiagnosticBag diagnostics)
    {
        var represented = new HashSet<ISymbol>(fields, SymbolEqualityComparer.Default);
        foreach (var tree in compilation.SyntaxTrees)
        {
            var model = compilation.Model(tree);
            foreach (var declaration in tree.GetRoot().DescendantNodes().OfType<PropertyDeclarationSyntax>())
                if (model.GetDeclaredSymbol(declaration) is { } property && Is(property, known) &&
                    !represented.Contains(property))
                    diagnostics.Error("PALCS0770", Locations.From(declaration),
                        "This [GhostField] declaration has no translated logical representation. " +
                        "Declare storage in a supported modeled or plain class, not an excluded declaration.");
        }
    }

    public static IrExpr? Initializer(IPropertySymbol property, WellKnown known,
        ImmutableDictionary<string, BoundSpec> bound, DiagnosticBag diagnostics)
    {
        if (!bound.TryGetValue(Key(property), out var spec)) return null;
        var value = new ExprLowerer(spec.Model, known, diagnostics, specPosition: true).Lower(spec.Expression);
        // No receiver/field environment is supplied by the shim. Additionally forbid
        // effects and stateful constructors: this value initializes logical storage only.
        if (ExprLowerer.HasEffect(value) || ExprLowerer.Subexpressions(value).Any(e =>
                e is IrAlloc or IrInlinePulse or IrCall { Kind: CalleeKind.Lemma }))
        {
            diagnostics.Error("PALCS0772", Locations.From(Declarations.ArgumentLocation(
                Declarations.Find(property, known.GhostFieldAttribute)!)),
                "A [GhostField] initializer must be a pure, independent specification expression.");
            return null;
        }
        known.GhostInitializers[Key(property)] = value;
        return value;
    }
}
