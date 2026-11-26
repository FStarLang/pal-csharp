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
        List<IrMethod>? lifted = null, INamedTypeSymbol? view = null, INamedTypeSymbol? ownerView = null)
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
        BorrowContext? ownerContext = null;
        HashSet<string>? ownerWritten = null;
        if (ownerView is not null)
        {
            var field = Borrowing.OwnerField(ownerView, known)!;
            ownerWritten = Borrowing.OwnerViewWrites(candidate.Syntax, model, self, ownerView, known);
            ownerContext = new BorrowContext(ownerView, field, known.MapType(ownerView)!,
                (IrClassType)known.MapType(field.Type)!, false, null) {
                ViewBase = Borrowing.ViewBase(ownerView, known),
                SelfName = "__pal_owner_view",
                PreservedFields = [.. ownerView.GetMembers().OfType<IFieldSymbol>()
                    .Concat(Borrowing.InheritedState(ownerView, known))
                    .Where(f => !f.IsStatic && !f.IsConst && !ownerWritten.Contains(f.Name))],
                PreservedGhost = [.. Borrowing.InheritedGhostState(ownerView, known)
                    .Where(p => !ownerWritten.Contains(p.Name))]
            };
            selfType = BorrowedOwners.Type(self, ownerView, known);
            ownerType = ownerContext.OwnerType;
        }
        var borrow = new BorrowContext(self, owner, selfType, ownerType, isCtor, ownerParameter)
            { Owned = Borrowing.OwnedFields(core, known), CorePath = corePath, ViewBase = viewBase, OwnerView = ownerContext };
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
            // A field of a struct the member holds in a local (`result.Count = …`) is
            // the local's, not the borrowed object's.
            if (wf.ContainingType.IsValueType && target is MemberAccessExpressionSyntax { Expression: var recv } &&
                model.GetSymbolInfo(recv).Symbol is ILocalSymbol) continue;
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
        if (ownerContext is { } context)
            leading = [leading[0], new IrParam(loc, context.SelfName, context.StructType, ParamMode.Ref), .. leading.Skip(1)];

        var iterated = Iterators.Element(symbol) is { } yielded ? known.MapType(yielded) : null;
        var returnType = iterated is not null ? new IrSeqType(iterated) :
            isCtor ? selfType : known.MapReturnType(ExactReturn(symbol, known) ?? symbol.ReturnType);
        if (!isCtor && viewBase is not null && symbol.ReturnType is INamedTypeSymbol resultRecord &&
            Borrowing.IsBorrowing(resultRecord, known) && resultRecord.TypeKind == TypeKind.Struct)
            returnType = BorrowedOwners.Type(resultRecord, self, known);
        if (returnType is null)
        {
            diagnostics.Unsupported(loc, $"The return type `{symbol.ReturnType}`");
            return null;
        }

        // R28.2. The borrowing field holds the receiver, before and after.
        IrExpr Holds(IrExpr structValue) =>
            new IrBinary(loc, BinOp.Eq,
                new IrField(loc, borrow.Core(structValue, known), owner.Name) {
                    Type = ownerContext is null ? ownerType : BorrowedOwners.Reference(ownerContext) },
                new IrRefOf(loc, ownerContext?.SelfName ?? Names.This) {
                    Type = ownerContext is null ? ownerType : BorrowedOwners.Reference(ownerContext) }) { Type = IrPrim.Bool };
        var selfVar = new IrVar(loc, BorrowContext.Self) { Type = selfType };
        // R27.37. Each owned field holds the object passed for it.
        IEnumerable<IrExpr> HoldsOwned(IrExpr structValue) => owned.Select(o =>
            (IrExpr)new IrBinary(loc, BinOp.Eq,
                new IrField(loc, borrow.Core(structValue, known), o.Field.Name) { Type = o.Type },
                new IrRefOf(loc, Borrowing.OwnedName(o.Field)) { Type = o.Type }) { Type = IrPrim.Bool });
        var requires = isCtor ? [] : ImmutableArray.Create([Holds(selfVar), .. HoldsOwned(selfVar)]);
        var ensures = ImmutableArray.CreateBuilder<IrExpr>();
        if (!isCtor && viewBase is not null &&
            symbol.ReturnType is INamedTypeSymbol { TypeKind: TypeKind.Struct } returnedRecord &&
            Borrowing.OwnerField(returnedRecord, known) is { } returnedOwner)
            ensures.Add(new IrBinary(loc, BinOp.Eq,
                new IrField(loc, new IrResult(loc) { Type = returnType }, returnedOwner.Name) {
                    Type = BorrowedOwners.Reference(borrow) },
                new IrRefOf(loc, borrow.SelfName) { Type = BorrowedOwners.Reference(borrow) }) { Type = IrPrim.Bool });
        if (ownerContext is { } oc)
        {
            var ownerValue = new IrVar(loc, oc.SelfName) { Type = oc.StructType };
            var ownsSource = new IrBinary(loc, BinOp.Eq,
                new IrField(loc, ownerValue, oc.Owner.Name) { Type = ownerType },
                new IrRefOf(loc, Names.This) { Type = ownerType }) { Type = IrPrim.Bool };
            requires = [.. requires, ownsSource];
            ensures.Add(ownsSource);
            // The extra retained-owner cell needs the same checked frame as a
            // direct view receiver. Readonly fields alone lose mutable coherence
            // state even when (for example) Current never writes that cell.
            if (ownerWritten!.Count == 0)
                ensures.Add(new IrBinary(loc, BinOp.Eq, ownerValue,
                    new IrOld(loc, ownerValue) { Type = oc.StructType }) { Type = IrPrim.Bool });
            foreach (var f in oc.Struct.GetMembers().OfType<IFieldSymbol>()
                .Concat(Borrowing.InheritedState(oc.Struct, known))
                .Where(f => !f.IsStatic && !f.IsConst && (f.IsReadOnly || !ownerWritten.Contains(f.Name))))
            {
                if (known.MapType(f.Type) is not { } fieldType) continue;
                var field = new IrField(loc, ownerValue, f.Name) { Type = fieldType };
                ensures.Add(new IrBinary(loc, BinOp.Eq, field, new IrOld(loc, field) { Type = field.Type }) { Type = IrPrim.Bool });
            }
            // The retained owner is a view record, not its underlying class.
            // Forward its untouched inherited ghost storage through constructors
            // and members just as direct view calls do. These are checked posts;
            // virtual/cache-writing calls retain their original body domain.
            foreach (var p in oc.PreservedGhost)
            {
                if (known.MapType(p.Type) is not { } fieldType) continue;
                var field = new IrField(loc, ownerValue, p.Name) { Type = fieldType };
                ensures.Add(new IrBinary(loc, BinOp.Eq, field, new IrOld(loc, field) { Type = fieldType })
                    { Type = IrPrim.Bool });
            }
        }
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
                // A factory can reach virtual members of this view from the
                // returned record's constructor. Without a transitive effect
                // summary, do not promise that mutable cache fields are unchanged.
                if (returnType is IrNamedType rt && rt.Name.Contains("_owner_", StringComparison.Ordinal))
                {
                    written.UnionWith(Borrowing.OwnerViewWrites(candidate.Syntax, model,
                        (INamedTypeSymbol)symbol.ReturnType, self, known));
                    foreach (var field in self.GetMembers().OfType<IFieldSymbol>()
                        .Concat(Borrowing.InheritedState(self, known)).Where(f => !f.IsReadOnly))
                        written.Add(field.Name);
                }
                borrow = borrow with {
                    PreservedGhost = [.. Borrowing.InheritedGhostState(self, known)
                        .Where(p => !written.Contains(p.Name))]
                };
                // A wholly unchanged view can retain the same reference-state
                // witness across calls and expression joins. This is a checked
                // postcondition, not an effect-analysis assumption.
                if (written.Count == 0)
                    ensures.Add(new IrBinary(loc, BinOp.Eq, selfVar,
                        new IrOld(loc, selfVar) { Type = selfType }) { Type = IrPrim.Bool });
                foreach (var f in self.GetMembers().OfType<IFieldSymbol>().Concat(Borrowing.InheritedState(self, known)))
                {
                    if (f.IsStatic || f.IsConst || borrow.IsOwner(f) || written.Contains(f.Name) ||
                        f.IsReadOnly && known.MapType(f.Type) is IrPrim ||
                        known.MapType(f.Type) is not { } fieldType) continue;
                    var field = new IrField(loc, selfVar, f.Name) { Type = fieldType };
                    ensures.Add(new IrBinary(loc, BinOp.Eq, field, new IrOld(loc, field) { Type = fieldType })
                        { Type = IrPrim.Bool });
                }
                foreach (var p in Borrowing.InheritedGhostState(self, known))
                {
                    if (written.Contains(p.Name) || known.MapType(p.Type) is not { } fieldType) continue;
                    var field = new IrField(loc, selfVar, p.Name) { Type = fieldType };
                    ensures.Add(new IrBinary(loc, BinOp.Eq, field, new IrOld(loc, field) { Type = fieldType })
                        { Type = IrPrim.Bool });
                }
            }
        }

        var lowerer = new StmtLowerer(model, known, diagnostics, ImmutableHashSet<string>.Empty, borrow);
        if (iterated is not null) lowerer.Iterate(iterated);
        // R32.11. A lambda a borrowing member passes to a `[Callback]` is lifted as any other's.
        lowerer.Expressions.LiftPrefix = known.Specialization?.Name ??
            (view is not null && known.Replica is { } rq ? rq.Name : Naming.Of(symbol));
        lowerer.Expressions.LiftTypeParameters =
            [.. WellKnown.AllTypeParameters(self).Select(t => t.Name), .. symbol.TypeParameters.Select(t => t.Name)];
        IrStmt? body;
        ImmutableArray<IrExpr> bodyRequires = [], bodyEnsures = [];
        // R20.2. An `[Admit]`ted member's body is not translated here either.
        var admitted = !isCtor && Declarations.Has(symbol, known.AdmitAttribute);
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
            body = admitted ? null : LowerBody(candidate.Syntax, lowerer, known, bound, diagnostics);
            var (br, be, trimmed) = ExtractBodyContracts(candidate.Syntax, model, known, lowerer, lowerRest: !admitted);
            bodyRequires = br;
            bodyEnsures = be;
            body = trimmed ?? body;
            if (body is not null && lowerer.Expressions.HoistedCells.Count > 0)
                body = new IrBlock(body.Loc, [
                    .. lowerer.Expressions.HoistedCells.Values.OrderBy(d => d.Name, StringComparer.Ordinal),
                    .. body is IrBlock hoistedBody ? hoistedBody.Statements : [body]]);
            if (body is not null && candidate.Syntax.DescendantNodes().Any(n =>
                    n is WhileStatementSyntax or ForStatementSyntax or DoStatementSyntax or CommonForEachStatementSyntax))
                body = new IrBlock(body.Loc, [.. BorrowFacts.Snapshots(borrow, known, loc),
                    .. body is IrBlock snapshotBody ? snapshotBody.Statements : [body]]);
        }

        if (!specs.ProtocolRequires.IsEmpty)
        {
            if (specs.Requires.Concat(specs.Ensures).Concat(specs.Preserves)
                .Concat(bodyRequires).Concat(bodyEnsures).Any(e => e.Type is IrPrim { Kind: PrimKind.SlProp }))
                diagnostics.Error("PALCS0866", loc,
                    "Enumeration protocol domain extension currently supports pure authored clauses; " +
                    "additional ownership alternatives need an explicit separating protocol.");
            IrExpr And(IEnumerable<IrExpr> xs) => xs.Aggregate(
                (IrExpr)new IrLiteral(loc, true) { Type = IrPrim.Bool },
                (a, b) => new IrBinary(loc, BinOp.And, a, b) { Type = IrPrim.Bool });
            IrExpr Implies(IrExpr a, IrExpr b) =>
                new IrBinary(loc, BinOp.Implies, a, b) { Type = IrPrim.Bool };
            var original = And(specs.Requires.Concat(bodyRequires));
            var protocol = And(specs.ProtocolRequires);
            var oldOriginal = new IrOld(loc, original) { Type = IrPrim.Bool };
            var oldProtocol = new IrOld(loc, protocol) { Type = IrPrim.Bool };
            // Verify BOTH domains. Protocol readiness must not erase a public
            // member's stale-version or other exceptional behavior. Conversely
            // an authored end-only precondition must not hide partial disposal.
            specs = specs with {
                Requires = [new IrBinary(loc, BinOp.Or, original, protocol) { Type = IrPrim.Bool }],
                Ensures = [
                    .. specs.Ensures.Concat(specs.Preserves).Concat(bodyEnsures).Select(e => Implies(oldOriginal, e)),
                    .. specs.ProtocolEnsures.Select(e => Implies(oldProtocol, e))
                ],
                Preserves = [],
                // A protocol operation is total on its ready domain. Exceptions
                // are still verified on the original domain outside readiness.
                Throws = [.. specs.Throws.Select(t => t with { When = And([
                    original, new IrUnary(loc, UnOp.Not, protocol) { Type = IrPrim.Bool },
                    t.When ?? new IrLiteral(loc, true) { Type = IrPrim.Bool }
                ]) })]
            };
            bodyRequires = [];
            bodyEnsures = [];
        }

        ImmutableArray<string> typeParameters =
            [.. WellKnown.AllTypeParameters(self).Select(t => t.Name), .. symbol.TypeParameters.Select(t => t.Name)];
        // A direct getter of the borrowing record's own field does not read the
        // borrowed object. Its pointer still identifies the owner, but ownership is
        // needed only if a contract observes that owner's model.
        var returned = body switch
        {
            IrReturn ret => ret.Value,
            IrBlock { Statements: [IrReturn ret] } => ret.Value,
            _ => null,
        };
        var clauses = specs.Requires.Concat(specs.Ensures).Concat(specs.Preserves)
            .Concat(bodyRequires).Concat(bodyEnsures)
            .Concat(specs.Throws.Select(t => t.When).OfType<IrExpr>())
            .Concat(specs.Decreases is { } measure ? [measure] : []);
        if (symbol.MethodKind == MethodKind.PropertyGet &&
            returned is IrField { Receiver: IrVar { Name: BorrowContext.Self } } &&
            returnType is not IrClassType { Plain: false } &&
            !clauses.SelectMany(Passes.Check.Subexpressions).Any(e =>
                e is IrVar { Name: Names.This or "$permission" } or IrInlinePulse or IrStmtExpr))
            leading[0] = leading[0] with { Plain = true };
        lifted?.AddRange(lowerer.Expressions.Lifted);
        return new IrMethod(
            loc, Naming.Of(symbol), [.. leading, .. parameters], returnType,
            [.. requires, .. specs.Requires, .. bodyRequires],
            [.. ensures, .. specs.Ensures, .. bodyEnsures],
            specs.Decreases, iterated is not null && body is not null ? lowerer.WrapIterator(body) : body)
        {
            IsIterator = iterated is not null,
            Preserves = specs.Preserves,
            Admit = admitted,
            UnconditionalEnsures = ensures.Count,
            Throws = specs.Throws,
            DeclaringClass = ((INamedTypeSymbol)owner.Type).Name,
            IsReadOnly = !writesOwner,
            TypeParameters = typeParameters,
            DefaultedTypeParameters = [.. typeParameters.Where(lowerer.Defaulted)],
            RlimitFactor = Declarations.Find(symbol, known.RlimitAttribute) is { ConstructorArguments: [{ Value: int factor }] } && factor > 0
                ? factor : null,
            InitialFuel = InitialFuel(symbol, known, loc, diagnostics),
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
