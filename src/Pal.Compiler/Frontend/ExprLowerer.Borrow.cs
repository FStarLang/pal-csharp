using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using Pal.Compiler.Emit;
using Pal.Compiler.Ir;

namespace Pal.Compiler.Frontend;

/// <summary>
/// §28. What a member of a borrowing struct (R28.1) is lowered against: the struct, the
/// field that borrows, and — for a constructor — the parameter the borrowed object arrives
/// in.
/// </summary>
public sealed record BorrowContext(
    INamedTypeSymbol Struct,
    IFieldSymbol Owner,
    IrType StructType,
    IrClassType OwnerType,
    bool Constructor,
    IParameterSymbol? OwnerParameter)
{
    /// <summary>R28.2. The IR name of the struct a member is called on.</summary>
    public const string Self = "self";

    public bool IsOwner(IFieldSymbol f) =>
        SymbolEqualityComparer.Default.Equals(f.OriginalDefinition, Owner.OriginalDefinition);

    public bool IsState(IFieldSymbol f) =>
        !f.IsStatic && !f.IsConst &&
        SymbolEqualityComparer.Default.Equals(f.ContainingType.OriginalDefinition, Struct.OriginalDefinition);
}

public sealed partial class ExprLowerer
{
    /// <summary>R28.2. Set while lowering a member of a borrowing struct, or its contract.</summary>
    public BorrowContext? Borrow { get; init; }

    /// <summary>
    /// R28.2. A ghost statement in a borrowing member's body, where the borrowed object is
    /// unfolded and its fields, like the method's own class's (§4.5), are readable.
    /// </summary>
    public bool BorrowBody { get; init; }

    private IrVar BorrowedObject(IrLoc loc) => new(loc, Names.This) { Type = Borrow!.OwnerType };

    private IrExpr SelfExpr(IrLoc loc) =>
        Borrow!.Constructor
            ? new IrResult(loc) { Type = Borrow.StructType }
            : new IrVar(loc, BorrowContext.Self) { Type = Borrow.StructType };

    private static bool IsShim(ISymbol? s) =>
        s?.Name.StartsWith(SpecBinder.ShimMethodPrefix, StringComparison.Ordinal) == true;

    /// <summary>
    /// R28.2. A name inside a borrowing struct's member: <c>@this</c> is the struct, the
    /// borrowing field is the borrowed object — the receiver of the translated member —
    /// and any other field is a field of the struct.
    /// </summary>
    private IrExpr? BorrowedIdentifier(ISymbol? symbol, IdentifierNameSyntax node, IrLoc loc)
    {
        if (Borrow is not { } bw) return null;
        switch (symbol)
        {
            case IParameterSymbol { Name: Names.This } p when IsShim(p.ContainingSymbol):
                return SelfExpr(loc);
            case IParameterSymbol p when bw.OwnerParameter is { } op &&
                (SymbolEqualityComparer.Default.Equals(p, op) || (IsShim(p.ContainingSymbol) && p.Name == op.Name)):
                return BorrowedObject(loc);
            case IFieldSymbol f when bw.IsOwner(f):
                return BorrowedObject(loc);
            case IFieldSymbol f when bw.IsState(f):
                if (bw.Constructor && !SpecPosition)
                {
                    diagnostics.Error("PALCS0732", loc,
                        $"The constructor of `{bw.Struct.Name}` reads its field `{f.Name}`. A borrowing " +
                        "struct's constructor is translated as the value it builds, so each field's " +
                        "initialiser may read the parameters and the borrowed object only " +
                        "(doc/translation.md R28.5).");
                    return new IrLiteral(loc, null);
                }
                return new IrField(loc, SelfExpr(loc), f.Name) { Type = known.MapType(f.Type) };
            default:
                return null;
        }
    }

    /// <summary>
    /// R28.2. <c>x.f</c> inside a borrowing struct's member, when <c>x</c> is the struct and
    /// <c>f</c> the borrowing field (the borrowed object), or <c>x</c> is the borrowed
    /// object and <c>f</c> one of its fields (a read of the opened receiver, R3.8).
    /// </summary>
    private IrExpr? BorrowedMember(MemberAccessExpressionSyntax node, ISymbol? symbol, IrLoc loc)
    {
        if (Borrow is not { } bw || symbol is not IFieldSymbol { IsStatic: false } f) return null;
        if (bw.IsOwner(f) && node.Expression is ThisExpressionSyntax) return BorrowedObject(loc);
        if (bw.IsState(f) && node.Expression is ThisExpressionSyntax)
            return BorrowedIdentifier(f, SyntaxFactory_Identifier(node), loc);
        if (bw.IsOwner(f) && model.GetSymbolInfo(node.Expression).Symbol is IParameterSymbol { Name: Names.This } sp &&
            IsShim(sp.ContainingSymbol) && !bw.Constructor)
            return BorrowedObject(loc);
        // R29.3. `@this.f` in a contract of a borrowing class's member: a field of the record.
        if (bw.Struct.TypeKind == TypeKind.Class && (bw.IsState(f) || bw.IsOwner(f)) &&
            model.GetSymbolInfo(node.Expression).Symbol is IParameterSymbol { Name: Names.This } cp && IsShim(cp.ContainingSymbol))
            return new IrField(loc, SelfExpr(loc), f.Name) { Type = known.MapType(f.Type) };
        if (SpecPosition && !BorrowBody) return null;
        if (SymbolEqualityComparer.Default.Equals(f.ContainingType.OriginalDefinition, bw.Owner.Type.OriginalDefinition) &&
            Lower(node.Expression) is IrVar { Name: Names.This })
            return new IrField(loc, BorrowedObject(loc), f.Name) { Type = known.MapType(f.Type) };
        return null;
    }

    private static IdentifierNameSyntax SyntaxFactory_Identifier(MemberAccessExpressionSyntax node) =>
        node.Name as IdentifierNameSyntax ?? Microsoft.CodeAnalysis.CSharp.SyntaxFactory.IdentifierName(node.Name.Identifier);

    /// <summary>
    /// R28.3. <c>ReferenceEquals(a, b)</c> in a contract: identity of two references. An
    /// operand is a parameter of class type — its Pulse binder, not its model — or a
    /// borrowing field of a struct value, which holds the reference.
    /// </summary>
    private IrExpr LowerReferenceEquals(InvocationExpressionSyntax node, IrLoc loc)
    {
        IrExpr Operand(ExpressionSyntax e)
        {
            var lowered = Lower(e);
            switch (lowered)
            {
                case IrVar { Type: IrClassType } v when model.GetSymbolInfo(e).Symbol is IParameterSymbol || v.Name == Names.This:
                    return new IrRefOf(lowered.Loc, v.Name) { Type = v.Type };
                case IrField { Type: IrClassType, Receiver.Type: IrNamedType }:
                    return lowered;
                default:
                    diagnostics.Error("PALCS0733", Locations.From(e),
                        $"`{e}` in `ReferenceEquals`. Reference identity can be stated of a parameter " +
                        "of class type and of a struct's borrowing field (doc/translation.md R28.3).");
                    return new IrLiteral(lowered.Loc, null);
            }
        }
        var args = node.ArgumentList.Arguments;
        return new IrBinary(loc, BinOp.Eq, Operand(args[0].Expression), Operand(args[1].Expression))
            { Type = IrPrim.Bool };
    }

    /// <summary>
    /// R28.4. <c>new S(owner, a…)</c> for a borrowing struct <c>S</c>: a read-only call of
    /// the constructor's translation, a method of the borrowed object's class, with the
    /// borrowed object as its receiver and the remaining arguments in order.
    /// </summary>
    private IrExpr BorrowingConstruction(
        BaseObjectCreationExpressionSyntax node, IMethodSymbol ctor, INamedTypeSymbol named, IrLoc loc)
    {
        var owner = Borrowing.OwnerField(named, known)!;
        if (Borrowing.OwnerParameter(ctor, owner) is not { } op || node.ArgumentList is null ||
            node.Initializer is not null)
        {
            diagnostics.Error("PALCS0730", loc,
                $"`{node}`. A borrowing struct is created by a constructor that assigns its borrowing " +
                "field from a parameter, without an object initializer (doc/translation.md R28.4).");
            return new IrLiteral(loc, null);
        }
        var receiver = default(IrExpr);
        var rest = new List<IrExpr>();
        var types = new List<IrType?> { null };
        foreach (var a in node.ArgumentList.Arguments)
        {
            var p = model.GetOperation(a) is Microsoft.CodeAnalysis.Operations.IArgumentOperation ao ? ao.Parameter : null;
            if (SymbolEqualityComparer.Default.Equals(p, op)) receiver = Lower(a.Expression);
            else { rest.Add(Lower(a.Expression)); types.Add(p is null ? null : known.MapType(p.Type)); }
        }
        if (receiver is null) return new IrLiteral(loc, null);
        var targs = WellKnown.AllTypeArguments(named).Select(known.MapType).ToList();
        return new IrCall(loc, Naming.Of(ctor), [receiver, .. rest])
        {
            Kind = CalleeKind.Method,
            ResultType = known.MapType(named),
            HasReceiver = true,
            ParamTypes = [.. types],
            TypeArguments = targs.All(t => t is not null) ? [.. targs.Select(t => t!)] : [],
            MutatesReceiver = false,
        };
    }

    /// <summary>
    /// R28.5. The body of a borrowing struct's constructor, which must assign each field it
    /// sets once from the parameters and the borrowed object: the struct value it builds.
    /// </summary>
    public IrStmt BorrowingConstructorBody(ConstructorDeclarationSyntax ctor, IrLoc loc)
    {
        var bw = Borrow!;
        var given = new List<IrFieldInit>();
        // An expression-bodied constructor (`=> _queue = queue`) is its one expression; it is
        // read in place, because a statement synthesised around it is in no syntax tree.
        IEnumerable<(SyntaxNode Node, ExpressionSyntax? Expr)> steps = ctor.ExpressionBody is { } eb
            ? [(eb, eb.Expression)]
            : (ctor.Body?.Statements ?? default).Select(st =>
                ((SyntaxNode)st, st is ExpressionStatementSyntax es ? es.Expression : null));
        foreach (var (node, expr) in steps)
        {
            if (expr is AssignmentExpressionSyntax { Left: var left, Right: var right } a &&
                a.IsKind(Microsoft.CodeAnalysis.CSharp.SyntaxKind.SimpleAssignmentExpression) &&
                (left is IdentifierNameSyntax || left is MemberAccessExpressionSyntax { Expression: ThisExpressionSyntax }) &&
                model.GetSymbolInfo(left).Symbol is IFieldSymbol f && bw.IsState(f) &&
                given.All(g => g.Field != f.Name))
            {
                given.Add(new IrFieldInit(f.Name, Lower(right)));
                continue;
            }
            if (expr is InvocationExpressionSyntax inv &&
                model.GetSymbolInfo(inv).Symbol is IMethodSymbol { IsStatic: true } m &&
                known.IsPalIntrinsic(m))
                continue;
            diagnostics.Error("PALCS0730", Locations.From(node),
                $"`{node.ToString().Trim()}` in the constructor of `{bw.Struct.Name}`. A borrowing type's " +
                "constructor assigns each field at most once, and does nothing else (doc/translation.md R28.5).");
        }
        var value = Construct(loc, WellKnown.StructName(bw.Struct), bw.Struct, given);
        return new IrReturn(loc, value is IrNew n ? n with { Type = bw.StructType } : value);
    }
}

/// <summary>
/// R28.4. What a loop in a borrowing struct's member keeps without being told: the
/// borrowing field holds the receiver, and each readonly field keeps the value it had on
/// entry, which a snapshot taken at the top of the body names. A loop body sees its
/// invariant and nothing else, and these are facts of the member, not of the loop.
/// </summary>
public static class BorrowFacts
{
    public static string Snapshot(IFieldSymbol f) => $"__pal_entry_{f.Name}";

    private static IEnumerable<(IFieldSymbol Field, IrPrim Type)> ReadOnlyFields(BorrowContext borrow, WellKnown known) =>
        borrow.Struct.GetMembers().OfType<IFieldSymbol>()
            .Where(f => !f.IsStatic && !f.IsConst && f.IsReadOnly && !borrow.IsOwner(f))
            .Select(f => (f, known.MapType(f.Type) as IrPrim))
            .Where(x => x.Item2 is not null)
            .Select(x => (x.f, x.Item2!));

    public static IEnumerable<IrStmt> Snapshots(BorrowContext borrow, WellKnown known, IrLoc loc)
    {
        var self = new IrVar(loc, BorrowContext.Self) { Type = borrow.StructType };
        foreach (var (f, type) in ReadOnlyFields(borrow, known))
            yield return new IrGhostStmt(loc, GhostKind.Let, new IrField(loc, self, f.Name) { Type = type }, Snapshot(f))
                { Type = type };
    }

    public static IEnumerable<IrExpr> Invariants(BorrowContext borrow, WellKnown known, IrLoc loc)
    {
        var self = new IrVar(loc, BorrowContext.Self) { Type = borrow.StructType };
        yield return new IrBinary(loc, BinOp.Eq,
            new IrField(loc, self, borrow.Owner.Name) { Type = borrow.OwnerType },
            new IrRefOf(loc, Pal.Compiler.Emit.Names.This) { Type = borrow.OwnerType }) { Type = IrPrim.Bool };
        foreach (var (f, type) in ReadOnlyFields(borrow, known))
        {
            var snapshotType = type.IsMachineInt ? new IrPrim(PrimKind.SpecInt) : type;
            yield return new IrBinary(loc, BinOp.Eq, new IrField(loc, self, f.Name) { Type = type },
                new IrVar(loc, Snapshot(f)) { Type = snapshotType }) { Type = IrPrim.Bool };
        }
    }
}
