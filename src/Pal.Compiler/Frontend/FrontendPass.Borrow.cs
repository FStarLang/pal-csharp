using System.Collections.Immutable;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using Pal.Compiler.Diagnostics;
using Pal.Compiler.Emit;
using Pal.Compiler.Ir;

namespace Pal.Compiler.Frontend;

public static partial class FrontendPass
{
    /// <summary>
    /// §28. A member of a borrowing struct (R28.1) is translated as a read-only instance
    /// method of the borrowed object's class (R28.2): the object is its receiver, shared
    /// at a fraction; the struct is a second parameter, <c>ref</c> when the member writes
    /// it (R28.4); and the borrowing field is required to hold the receiver.
    /// </summary>
    private static IrDecl? LowerBorrowingMember(
        Candidate candidate, SemanticModel model, WellKnown known,
        ImmutableDictionary<string, BoundSpec> bound, DiagnosticBag diagnostics, IrLoc loc,
        List<IrMethod>? lifted = null, INamedTypeSymbol? view = null)
    {
        // The candidate's symbol is of the compilation before the spec shims were added;
        // the borrowing context is compared against symbols of this one.
        var symbol = model.GetDeclaredSymbol(candidate.Syntax) switch
        {
            IMethodSymbol m => m,
            IPropertySymbol p => p.GetMethod,
            _ => null,
        } ?? candidate.Symbol;
        // R32.13. A replica of a base member at a view is a member of the view.
        var self = view ?? symbol.ContainingType;
        var viewBase = Borrowing.ViewBase(self, known);
        // R32.12. A wrapping struct's member is one of the object its core borrows.
        var (corePath, core) = Borrowing.Innermost(self, known);
        var owner = Borrowing.OwnerField(core, known)!;
        // R35.3. Unless the core owns no objects and is created by a method of the owner's class.
        if (!corePath.IsEmpty && symbol.MethodKind == MethodKind.Constructor &&
            !(Borrowing.CreatableWrapping(self, known) && Borrowing.OwnerParameter(symbol, owner, known.Compilation) is not null))
        {
            diagnostics.Error("PALCS0801", loc,
                $"The constructor of the wrapping struct `{self.Name}`. A wrapping struct's members are " +
                "verified as members of the object its core borrows; its constructors are not " +
                "(doc/translation.md R32.12).");
            return null;
        }
        if (known.MapType(owner.Type) is not IrClassType ownerType || known.MapType(self) is not { } selfType)
        {
            diagnostics.Unsupported(loc, $"The borrowing struct `{self.Name}`");
            return null;
        }
        var isCtor = symbol.MethodKind == MethodKind.Constructor;
        var ownerParameter = isCtor ? Borrowing.OwnerParameter(symbol, owner, known.Compilation) : null;
        if (isCtor && ownerParameter is null)
        {
            diagnostics.Error("PALCS0730", loc,
                $"The constructor of `{self.Name}` does not assign `{owner.Name}` from a parameter. A " +
                "borrowing struct's constructor takes the object it borrows (doc/translation.md R28.4).");
            return null;
        }
        var borrow = new BorrowContext(self, owner, selfType, ownerType, isCtor, ownerParameter)
            { Owned = Borrowing.OwnedFields(core, known), CorePath = corePath, ViewBase = viewBase };
        // R27.37. Each object the struct owns is a further parameter of a member, owned
        // through its invariant as any object parameter is, and held by the field.
        var owned = ImmutableArray.CreateBuilder<(IFieldSymbol Field, IrClassType Type)>();
        foreach (var f in borrow.Owned)
        {
            if (known.MapType(f.Type) is not IrClassType ot)
            {
                diagnostics.Unsupported(loc, $"The field `{self.Name}.{f.Name}`");
                return null;
            }
            owned.Add((f, ot));
        }

        // R28.7. The borrowed object is shared: nothing of it is written.
        foreach (var node in candidate.Syntax.DescendantNodes())
        {
            var target = node switch
            {
                AssignmentExpressionSyntax a => a.Left,
                PrefixUnaryExpressionSyntax p when Borrowing.IsStep(p) => p.Operand,
                PostfixUnaryExpressionSyntax p when Borrowing.IsStep(p) => p.Operand,
                _ => null,
            };
            if (target is null || model.GetSymbolInfo(target).Symbol is not IFieldSymbol { IsStatic: false } wf ||
                borrow.IsState(wf)) continue;
            diagnostics.Error("PALCS0734", Locations.From(target),
                $"`{target}` is written in a member of `{self.Name}`, which borrows `{owner.Name}`. A " +
                "borrowing struct reads the object it borrows and never writes it (doc/translation.md R28.7).");
            return null;
        }

        // R32.13. A view's override has the contract of the member it overrides at the
        // view: what a caller of the base member at a view is promised.
        var overridden = view is null && viewBase is not null && !SpecAttributes(candidate.Declaration, known).Any()
            ? ViewOverridden(symbol, viewBase) : null;
        var specs = overridden is not null
            ? ReadSpecs(overridden, (ISymbol?)overridden.AssociatedSymbol ?? overridden, known, bound, diagnostics, borrow, self)
            : ReadSpecs(candidate.Symbol, candidate.Declaration, known, bound, diagnostics, borrow, view);
        var parameters = LowerParameters(symbol, model, known, diagnostics)
            .Where(p => ownerParameter is null || p.Name != ownerParameter.Name);
        // R32.13. A view's member takes its record by reference: what it reaches through a
        // virtual call is decided at the view, and so is what it writes.
        var writes = !isCtor && (viewBase is not null || Borrowing.WritesState(candidate.Syntax, model, self));
        // R32.13. A view's member that writes the object it borrows holds it exclusively.
        var writesOwner = viewBase is not null && !isCtor && Borrowing.WritesOwner(candidate.Syntax, model, self, known);
        IrParam[] leading = isCtor
            ? [new IrParam(loc, Names.This, ownerType, ParamMode.Value)]
            : [new IrParam(loc, Names.This, ownerType, ParamMode.Value),
               new IrParam(loc, BorrowContext.Self, selfType, writes ? ParamMode.Ref : ParamMode.Value),
               .. owned.Select(o => new IrParam(loc, Borrowing.OwnedName(o.Field), o.Type, ParamMode.Value))];

        var returnType = isCtor ? selfType : known.MapType(ExactReturn(symbol, known) ?? symbol.ReturnType);
        if (returnType is null)
        {
            diagnostics.Unsupported(loc, $"The return type `{symbol.ReturnType}`");
            return null;
        }

        // R28.2. The borrowing field holds the receiver, before and after.
        IrExpr Holds(IrExpr structValue) =>
            new IrBinary(loc, BinOp.Eq,
                new IrField(loc, borrow.Core(structValue, known), owner.Name) { Type = ownerType },
                new IrRefOf(loc, Names.This) { Type = ownerType }) { Type = IrPrim.Bool };
        var selfVar = new IrVar(loc, BorrowContext.Self) { Type = selfType };
        // R27.37. Each owned field holds the object passed for it.
        IEnumerable<IrExpr> HoldsOwned(IrExpr structValue) => owned.Select(o =>
            (IrExpr)new IrBinary(loc, BinOp.Eq,
                new IrField(loc, borrow.Core(structValue, known), o.Field.Name) { Type = o.Type },
                new IrRefOf(loc, Borrowing.OwnedName(o.Field)) { Type = o.Type }) { Type = IrPrim.Bool });
        var requires = isCtor ? [] : ImmutableArray.Create([Holds(selfVar), .. HoldsOwned(selfVar)]);
        var ensures = ImmutableArray.CreateBuilder<IrExpr>();
        if (isCtor) ensures.Add(Holds(new IrResult(loc) { Type = selfType }));
        // R32.13. So does a view another member returns.
        else if (ExactReturn(symbol, known) is { } exactView && Borrowing.IsView(exactView, known) &&
                 SymbolEqualityComparer.Default.Equals(Borrowing.OwnerField(exactView, known)?.Type.OriginalDefinition, owner.Type.OriginalDefinition))
            ensures.Add(Holds(new IrResult(loc) { Type = returnType }));
        else if (writes)
        {
            ensures.Add(Holds(selfVar));
            ensures.AddRange(HoldsOwned(selfVar));
            // R28.4. A readonly field of the struct is not written by its members. R32.12: nor
            // is one of a struct it wraps, whose members it calls.
            var levels = new List<(IrExpr Value, INamedTypeSymbol Type)> { (selfVar, self) };
            foreach (var pf in corePath)
                levels.Add((new IrField(loc, levels[^1].Value, pf.Name) { Type = known.MapType(pf.Type) }, (INamedTypeSymbol)pf.Type));
            foreach (var (level, levelType) in levels)
            foreach (var f in levelType.GetMembers().OfType<IFieldSymbol>())
            {
                if (f.IsStatic || f.IsConst || !f.IsReadOnly || borrow.IsOwner(f) ||
                    known.MapType(f.Type) is not IrPrim fieldType) continue;
                var field = new IrField(loc, level, f.Name) { Type = fieldType };
                ensures.Add(new IrBinary(loc, BinOp.Eq, field, new IrOld(loc, field) { Type = fieldType })
                    { Type = IrPrim.Bool });
            }
            // R32.14. A view's member leaves the fields of its record it never writes (in its
            // body, or in the members of the view it reaches) as they were.
            if (viewBase is not null)
            {
                var written = Borrowing.ViewWrites(candidate.Syntax, model, self, known);
                foreach (var f in self.GetMembers().OfType<IFieldSymbol>().Concat(Borrowing.InheritedState(self, known)))
                {
                    if (f.IsStatic || f.IsConst || borrow.IsOwner(f) || written.Contains(f.Name) ||
                        f.IsReadOnly && known.MapType(f.Type) is IrPrim ||
                        known.MapType(f.Type) is not { } fieldType) continue;
                    var field = new IrField(loc, selfVar, f.Name) { Type = fieldType };
                    ensures.Add(new IrBinary(loc, BinOp.Eq, field, new IrOld(loc, field) { Type = fieldType })
                        { Type = IrPrim.Bool });
                }
            }
        }

        var lowerer = new StmtLowerer(model, known, diagnostics, ImmutableHashSet<string>.Empty, borrow);
        // R32.11. A lambda a borrowing member passes to a `[Callback]` is lifted as any other's.
        lowerer.Expressions.LiftPrefix = view is not null && known.Replica is { } rq ? rq.Name : Naming.Of(symbol);
        lowerer.Expressions.LiftTypeParameters =
            [.. WellKnown.AllTypeParameters(self).Select(t => t.Name), .. symbol.TypeParameters.Select(t => t.Name)];
        IrStmt? body;
        ImmutableArray<IrExpr> bodyRequires = [], bodyEnsures = [];
        if (isCtor)
        {
            if (candidate.Syntax is ConstructorDeclarationSyntax { Initializer: { } init } chained &&
                init.ThisOrBaseKeyword.IsKind(Microsoft.CodeAnalysis.CSharp.SyntaxKind.ThisKeyword) &&
                chained.ExpressionBody is null && chained.Body is { Statements.Count: 0 })
                body = lowerer.Expressions.ChainedBorrowingConstructor(init, loc);
            else if (candidate.Syntax is not ConstructorDeclarationSyntax c ||
                     c.Initializer is { } ci && !(viewBase is not null && ci.ThisOrBaseKeyword.IsKind(Microsoft.CodeAnalysis.CSharp.SyntaxKind.BaseKeyword)))
            {
                diagnostics.Error("PALCS0730", loc,
                    $"The constructor of `{self.Name}` chains to another. A borrowing struct's constructor " +
                    "assigns its fields (doc/translation.md R28.5).");
                return null;
            }
            else body = lowerer.Expressions.BorrowingConstructorBody(c, loc);
        }
        else
        {
            body = LowerBody(candidate.Syntax, lowerer);
            var (br, be, trimmed) = ExtractBodyContracts(candidate.Syntax, model, known, lowerer, lowerRest: true);
            bodyRequires = br;
            bodyEnsures = be;
            body = trimmed ?? body;
            if (body is not null && candidate.Syntax.DescendantNodes().Any(n =>
                    n is WhileStatementSyntax or ForStatementSyntax or DoStatementSyntax or ForEachStatementSyntax))
                body = new IrBlock(body.Loc, [.. BorrowFacts.Snapshots(borrow, known, loc), body]);
        }

        ImmutableArray<string> typeParameters =
            [.. WellKnown.AllTypeParameters(self).Select(t => t.Name), .. symbol.TypeParameters.Select(t => t.Name)];
        lifted?.AddRange(lowerer.Expressions.Lifted);
        return new IrMethod(
            loc, Naming.Of(symbol), [.. leading, .. parameters], returnType,
            [.. requires, .. specs.Requires, .. bodyRequires],
            [.. ensures, .. specs.Ensures, .. bodyEnsures],
            specs.Decreases, body)
        {
            Preserves = specs.Preserves,
            UnconditionalEnsures = ensures.Count,
            Throws = specs.Throws,
            DeclaringClass = ((INamedTypeSymbol)owner.Type).Name,
            IsReadOnly = !writesOwner,
            TypeParameters = typeParameters,
            DefaultedTypeParameters = [.. typeParameters.Where(lowerer.Defaulted)],
            RlimitFactor = Declarations.Find(symbol, known.RlimitAttribute) is { ConstructorArguments: [{ Value: int factor }] } && factor > 0
                ? factor : null,
        };
    }

    /// <summary>R32.13. The member of the view's base a view member overrides.</summary>
    private static IMethodSymbol? ViewOverridden(IMethodSymbol symbol, INamedTypeSymbol viewBase)
    {
        for (var o = symbol.OverriddenMethod; o is not null; o = o.OverriddenMethod)
            if (SymbolEqualityComparer.Default.Equals(o.ContainingType.OriginalDefinition, viewBase.OriginalDefinition))
                return o;
        return null;
    }
}
