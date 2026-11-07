using System.Collections.Immutable;
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
    /// <summary>R27.37. The cell an extended borrowing constructor builds its struct in.</summary>
    public const string SelfCell = "__pal_self";

    /// <summary>R27.37. The struct's fields that own an object (<see cref="Borrowing.OwnedFields"/>).</summary>
    public ImmutableArray<IFieldSymbol> Owned { get; init; } = [];

    /// <summary>
    /// R27.41. The IR name the struct is read under: <c>self</c> in its own members, the
    /// local in an owner's method that holds one.
    /// </summary>
    public string SelfName { get; init; } = Self;

    /// <summary>
    /// R27.49. The IR name of the borrowed object: <c>this</c>, or, for a struct an owner's
    /// method holds of another object of its class, that object's parameter.
    /// </summary>
    public string OwnerName { get; init; } = Names.This;

    /// <summary>R27.41. The local each owned field's object is held in, when not the parameter's name.</summary>
    public ImmutableDictionary<string, string> OwnedNames { get; init; } = ImmutableDictionary<string, string>.Empty;

    public string OwnedLocal(IFieldSymbol f) =>
        OwnedNames.TryGetValue(f.Name, out var n) ? n : Borrowing.OwnedName(f);

    public bool IsOwned(IFieldSymbol f) =>
        Owned.Any(o => SymbolEqualityComparer.Default.Equals(o.OriginalDefinition, f.OriginalDefinition));

    public bool IsOwner(IFieldSymbol f) =>
        SymbolEqualityComparer.Default.Equals(f.OriginalDefinition, Owner.OriginalDefinition);

    public bool IsState(IFieldSymbol f) =>
        !f.IsStatic && !f.IsConst &&
        SymbolEqualityComparer.Default.Equals(f.ContainingType.OriginalDefinition, Struct.OriginalDefinition);
}

public sealed partial class ExprLowerer
{
    private readonly BorrowContext? _borrow;
    private BorrowContext? _heldAs;

    /// <summary>
    /// R28.2. Set while lowering a member of a borrowing struct, or its contract; R27.41,
    /// also while expanding a <c>[Spec]</c> member of a struct an owner's method holds.
    /// </summary>
    public BorrowContext? Borrow { get => _heldAs ?? _borrow; init => _borrow = value; }

    /// <summary>
    /// R28.2. A ghost statement in a borrowing member's body, where the borrowed object is
    /// unfolded and its fields, like the method's own class's (§4.5), are readable.
    /// </summary>
    public bool BorrowBody { get; init; }

    private IrVar BorrowedObject(IrLoc loc) => new(loc, Borrow!.OwnerName) { Type = Borrow!.OwnerType };

    /// <summary>R27.49. The heap of a region class: the borrowed object's, inside a held struct of another owner.</summary>
    private string HeapVarName(string regionClass) =>
        Region.HeapNameOf(regionClass, Borrow?.OwnerName ?? Names.This);

    private IrVar OwnedObject(IFieldSymbol f, IrLoc loc) =>
        new(loc, Borrow!.OwnedLocal(f)) { Type = known.MapType(f.Type) };

    private IrExpr SelfExpr(IrLoc loc) =>
        Borrow!.Constructor
            ? new IrResult(loc) { Type = Borrow.StructType }
            : new IrVar(loc, Borrow.SelfName) { Type = Borrow.StructType };

    // R27.41. The borrowing structs this method holds in locals, by local.
    private readonly Dictionary<ISymbol, BorrowContext> _held = new(SymbolEqualityComparer.Default);
    private int _inlineDepth;

    /// <summary>R27.41. Records that <paramref name="local"/> holds a borrowing struct of the method's own object.</summary>
    public void Hold(ILocalSymbol local, BorrowContext held) => _held[local] = held;

    /// <summary>R27.41. The borrowing structs held so far, in declaration order.</summary>
    public IEnumerable<BorrowContext> Held => _held.Values;

    // R27.51. The enumerator structs `foreach` statements over owners hold, by iteration variable.
    private readonly Dictionary<ISymbol, BorrowContext> _foreachHeld = new(SymbolEqualityComparer.Default);

    /// <summary>R27.51. Records that the `foreach` declaring <paramref name="variable"/> holds the enumerator <paramref name="held"/>.</summary>
    public void HoldForEach(ILocalSymbol variable, BorrowContext held) => _foreachHeld[variable] = held;

    private BorrowContext? HeldContext(ExpressionSyntax e) =>
        model.GetSymbolInfo(Unparenthesized(e)).Symbol is ILocalSymbol l && _held.TryGetValue(l, out var c) ? c
        : ForEachEnumerator(Unparenthesized(e));

    /// <summary>R27.51. <c>Pal.Enumerator&lt;E&gt;(x)</c>, in a contract: the enumerator of the `foreach` over <c>x</c>.</summary>
    private BorrowContext? ForEachEnumerator(ExpressionSyntax e) =>
        SpecPosition && e is InvocationExpressionSyntax { ArgumentList.Arguments: [{ Expression: IdentifierNameSyntax x }] } call &&
        model.GetSymbolInfo(call).Symbol is IMethodSymbol { Name: nameof(PalLang.Pal.Enumerator) } m && known.IsPalIntrinsic(m) &&
        model.GetSymbolInfo(x).Symbol is ILocalSymbol v && _foreachHeld.TryGetValue(v, out var c) &&
        SymbolEqualityComparer.Default.Equals(m.TypeArguments[0].OriginalDefinition, c.Struct.OriginalDefinition)
            ? c : null;

    /// <summary>R27.51. A call of the member <paramref name="callee"/> of the held enumerator <paramref name="held"/>.</summary>
    public IrExpr HeldCallOf(BorrowContext held, IMethodSymbol callee, IrLoc loc) =>
        WithHeld(held, () => HeldCall(held, callee, [], loc));

    private T WithHeld<T>(BorrowContext held, Func<T> f)
    {
        var saved = _heldAs;
        _heldAs = held;
        try { return f(); }
        finally { _heldAs = saved; }
    }

    /// <summary>
    /// R27.41. <c>e.M(a…)</c> on a borrowing struct the method holds in a local: the
    /// member's translation applied to the method's own object, the local (by reference
    /// when the member writes the struct), the objects the local's struct owns, and the
    /// arguments. <c>null</c> when the receiver is not such a local.
    /// </summary>
    private IrExpr? HeldInvocation(InvocationExpressionSyntax node, IMethodSymbol method, IrLoc loc)
    {
        if (node.Expression is not MemberAccessExpressionSyntax { Expression: var receiver } ||
            HeldContext(receiver) is not { } held)
            return null;
        if (SpecPosition || !Borrowing.IsMember(method, known) || method.IsStatic)
            return HeldRefused(node, loc);
        var args = node.ArgumentList.Arguments.Select(a => Lower(a.Expression)).ToList();
        return WithHeld(held, () => HeldCall(held, method, args, loc));
    }

    /// <summary>
    /// R27.41. <c>e.P</c> on a held borrowing struct: in code, a call of the getter; in a
    /// contract, a <c>[Spec]</c> property's body with the struct read as the local.
    /// </summary>
    private IrExpr? HeldMember(MemberAccessExpressionSyntax node, ISymbol? symbol, IrLoc loc)
    {
        if (symbol is IMethodSymbol || HeldContext(node.Expression) is not { } held) return null;
        if (symbol is IPropertySymbol sp && SpecPosition && Declarations.Has(sp, known.SpecAttribute))
            return InlineSpec(held, sp, loc) ?? HeldRefused(node, loc);
        if (symbol is IPropertySymbol { GetMethod: { } getter, IsStatic: false } && !SpecPosition &&
            Borrowing.IsMember(getter, known))
            return WithHeld(held, () => HeldCall(held, getter, [], loc));
        return HeldRefused(node, loc);
    }

    private IrExpr HeldRefused(ExpressionSyntax node, IrLoc loc)
    {
        diagnostics.Error("PALCS0710", loc,
            $"`{node}`. Of a borrowing struct held in a local, code may call its members and a " +
            "contract may read its expression-bodied `[Spec]` properties (doc/translation.md R27.41).");
        return new IrLiteral(loc, null);
    }

    private IrExpr HeldCall(BorrowContext held, IMethodSymbol callee, IReadOnlyList<IrExpr> args, IrLoc loc)
    {
        var decl = callee.DeclaringSyntaxReferences.FirstOrDefault()?.GetSyntax();
        if (decl?.Parent is AccessorListSyntax { Parent: { } owner }) decl = owner;
        if (decl is ArrowExpressionClauseSyntax { Parent: { } arrowOwner }) decl = arrowOwner;
        var local = new IrVar(loc, held.SelfName) { Type = held.StructType };
        IrExpr self = decl is not null &&
                      Borrowing.WritesState(decl, model.Compilation.GetSemanticModel(decl.SyntaxTree), held.Struct)
            ? new IrRefArg(loc, local)
            : local;
        return BorrowingCall(callee, self, args, loc);
    }

    /// <summary>
    /// R27.41. A <c>[Spec]</c> property of a borrowing struct, read in a contract, is its
    /// body: an abbreviation, expanded where it is read, with the struct, its borrowed
    /// object and its owned objects those of the reader's context.
    /// </summary>
    private IrExpr? InlineSpec(BorrowContext held, IPropertySymbol property, IrLoc loc)
    {
        var body = property.DeclaringSyntaxReferences.FirstOrDefault()?.GetSyntax() switch
        {
            PropertyDeclarationSyntax { ExpressionBody.Expression: var e } => e,
            _ => null,
        };
        if (body is null || _inlineDepth > 16) return null;
        var nested = new ExprLowerer(model.Compilation.GetSemanticModel(body.SyntaxTree), known, diagnostics, specPosition: true)
        {
            Borrow = held,
            ObjectFields = ObjectFields,
        };
        nested._inlineDepth = _inlineDepth + 1;
        return nested.Lower(body);
    }

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
            // R27.41. A `[Spec]` property of the struct, in a contract.
            case IPropertySymbol { IsStatic: false } sp when SpecPosition && Declarations.Has(sp, known.SpecAttribute) &&
                SymbolEqualityComparer.Default.Equals(sp.ContainingType.OriginalDefinition, bw.Struct.OriginalDefinition):
                return InlineSpec(bw, sp, loc);
            // R27.37. An owned object is a parameter of every member but the constructor.
            case IFieldSymbol f when bw.IsOwned(f) && !bw.Constructor:
                return OwnedObject(f, loc);
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
        if (Borrow is { } sb && symbol is IPropertySymbol && node.Expression is ThisExpressionSyntax)
            return BorrowedIdentifier(symbol, SyntaxFactory_Identifier(node), loc);
        if (Borrow is not { } bw || symbol is not IFieldSymbol { IsStatic: false } f) return null;
        if (bw.IsOwner(f) && node.Expression is ThisExpressionSyntax) return BorrowedObject(loc);
        if (bw.IsOwned(f) && !bw.Constructor &&
            (node.Expression is ThisExpressionSyntax ||
             model.GetSymbolInfo(node.Expression).Symbol is IParameterSymbol { Name: Names.This } op && IsShim(op.ContainingSymbol)))
            return OwnedObject(f, loc);
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
            // R29.4. The operands are converted to `object`; identity is of the reference itself.
            lowered = Unboxed(lowered);
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
    /// R29.4. A call, inside a member of a borrowing type, of another member of the same
    /// type that does not write its state (<c>object IEnumerator.Current =&gt; Current</c>):
    /// the callee's translation applied to the same borrowed object and the same value of
    /// the struct or record. <c>null</c> when the call is not one.
    /// </summary>
    private IrExpr? BorrowingSelfCall(IMethodSymbol callee, IReadOnlyList<ExpressionSyntax> args, IrLoc loc)
    {
        if (Borrow is not { Constructor: false } bw || SpecPosition) return null;
        if (callee is { IsStatic: true } or { MethodKind: MethodKind.Constructor }) return null;
        if (!SymbolEqualityComparer.Default.Equals(callee.ContainingType.OriginalDefinition, bw.Struct.OriginalDefinition))
            return null;
        if (!Borrowing.IsMember(callee, known) || Declarations.KindOf(callee, known) is null) return null;
        if (callee.DeclaringSyntaxReferences.FirstOrDefault()?.GetSyntax() is not { } decl) return null;
        // A property getter's declaring syntax may be its accessor or its arrow clause; the
        // property is the unit whose body R28.4's test reads.
        if (decl.Parent is AccessorListSyntax { Parent: { } owner }) decl = owner;
        if (decl is ArrowExpressionClauseSyntax { Parent: { } arrowOwner }) decl = arrowOwner;
        // R27.37. A member that writes the struct is passed the caller's own `ref`; the
        // caller writes it too (Borrowing.WritesState counts the call).
        var self = Borrowing.WritesState(decl, model.Compilation.GetSemanticModel(decl.SyntaxTree), bw.Struct)
            ? new IrRefArg(loc, new IrVar(loc, BorrowContext.Self) { Type = bw.StructType })
            : SelfExpr(loc);
        return BorrowingCall(callee, self, args.Select(Lower), loc);
    }

    /// <summary>
    /// R28.2/R27.37. A call of a borrowing member's translation: the borrowed object, the
    /// struct (a value, or a <c>ref</c> when the callee writes it), each owned object, then
    /// the arguments.
    /// </summary>
    private IrCall BorrowingCall(IMethodSymbol callee, IrExpr self, IEnumerable<IrExpr> args, IrLoc loc)
    {
        var bw = Borrow!;
        var targs = WellKnown.AllTypeArguments(bw.Struct).Select(known.MapType).ToList();
        var owned = bw.Owned.Select(f => OwnedObject(f, loc)).ToList();
        return new IrCall(loc, Naming.Of(callee), [BorrowedObject(loc), self, .. owned, .. args])
        {
            Kind = CalleeKind.Method,
            ResultType = known.MapType(callee.ReturnType),
            HasReceiver = true,
            ParamTypes = [null, null, .. owned.Select(o => o.Type), .. callee.Parameters.Select(p => known.MapType(p.Type))],
            TypeArguments = targs.All(t => t is not null) ? [.. targs.Select(t => t!)] : [],
            MutatesReceiver = false,
        };
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
        if (Borrowing.OwnerParameter(ctor, owner, known.Compilation) is not { } op || node.ArgumentList is null ||
            node.Initializer is not null)
        {
            diagnostics.Error("PALCS0730", loc,
                $"`{node}`. A borrowing struct is created by a constructor that assigns its borrowing " +
                "field from a parameter, without an object initializer (doc/translation.md R28.4).");
            return new IrLiteral(loc, null);
        }
        return ConstructorCall(node.ArgumentList, ctor, named, op, loc);
    }

    /// <summary>
    /// R27.38. A chaining constructor of a borrowing struct (<c>: this(set, false) { }</c>)
    /// is the struct the constructor it chains to builds: its body returns that call.
    /// </summary>
    public IrStmt ChainedBorrowingConstructor(ConstructorInitializerSyntax init, IrLoc loc)
    {
        var bw = Borrow!;
        if (model.GetSymbolInfo(init).Symbol is not IMethodSymbol target ||
            Borrowing.OwnerParameter(target, bw.Owner, known.Compilation) is not { } op)
            return new IrReturn(loc, new IrLiteral(loc, null));
        return new IrReturn(loc, ConstructorCall(init.ArgumentList, target, bw.Struct, op, loc));
    }

    private IrExpr ConstructorCall(ArgumentListSyntax argList, IMethodSymbol ctor, INamedTypeSymbol named,
        IParameterSymbol op, IrLoc loc)
    {
        var receiver = default(IrExpr);
        var rest = new List<IrExpr>();
        var types = new List<IrType?> { null };
        foreach (var a in argList.Arguments)
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
    /// R27.37. With an owned field, it may also call methods (of the borrowed or an owned
    /// object) between the assignments, and end by calling members of the struct itself: an
    /// owned field's object is a local, and the struct is built in a local the trailing
    /// calls write by reference.
    /// </summary>
    public IrStmt BorrowingConstructorBody(ConstructorDeclarationSyntax ctor, IrLoc loc)
    {
        var bw = Borrow!;
        var given = new List<IrFieldInit>();
        var extended = !bw.Owned.IsEmpty;
        var prefix = new List<IrStmt>();
        var tail = new List<(IMethodSymbol Callee, InvocationExpressionSyntax Call)>();
        // An expression-bodied constructor (`=> _queue = queue`) is its one expression; it is
        // read in place, because a statement synthesised around it is in no syntax tree.
        IEnumerable<(SyntaxNode Node, ExpressionSyntax? Expr)> steps = ctor.ExpressionBody is { } eb
            ? [(eb, eb.Expression)]
            : (ctor.Body?.Statements ?? default).Select(st =>
                ((SyntaxNode)st, st is ExpressionStatementSyntax es ? es.Expression : null));
        foreach (var (node, expr) in steps)
        {
            if (tail.Count == 0 &&
                expr is AssignmentExpressionSyntax { Left: var left, Right: var right } a &&
                a.IsKind(Microsoft.CodeAnalysis.CSharp.SyntaxKind.SimpleAssignmentExpression) &&
                (left is IdentifierNameSyntax || left is MemberAccessExpressionSyntax { Expression: ThisExpressionSyntax }) &&
                model.GetSymbolInfo(left).Symbol is IFieldSymbol f && bw.IsState(f) &&
                given.All(g => g.Field != f.Name))
            {
                var value = Lower(right);
                if (extended && (bw.IsOwned(f) || ContainsCall(value)) && known.MapType(f.Type) is { } ft)
                {
                    var local = bw.IsOwned(f) ? Borrowing.OwnedName(f) : "__pal_init" + f.Name;
                    prefix.Add(new IrLocalDecl(Locations.From(node), local, ft, value));
                    value = new IrVar(loc, local) { Type = ft };
                }
                given.Add(new IrFieldInit(f.Name, value));
                continue;
            }
            if (expr is InvocationExpressionSyntax inv &&
                model.GetSymbolInfo(inv).Symbol is IMethodSymbol { IsStatic: true } m &&
                known.IsPalIntrinsic(m))
                continue;
            if (extended && expr is InvocationExpressionSyntax call &&
                model.GetSymbolInfo(call).Symbol is IMethodSymbol callee)
            {
                if (call.Expression is IdentifierNameSyntax or MemberAccessExpressionSyntax { Expression: ThisExpressionSyntax } &&
                    !callee.IsStatic && Borrowing.IsMember(callee, known) &&
                    SymbolEqualityComparer.Default.Equals(callee.ContainingType.OriginalDefinition, bw.Struct.OriginalDefinition))
                {
                    tail.Add((callee, call));
                    continue;
                }
                if (tail.Count == 0)
                {
                    prefix.Add(new IrExprStmt(Locations.From(node), Lower(call)));
                    continue;
                }
            }
            diagnostics.Error("PALCS0730", Locations.From(node),
                $"`{node.ToString().Trim()}` in the constructor of `{bw.Struct.Name}`. A borrowing type's " +
                "constructor assigns each field at most once, and does nothing else (doc/translation.md R28.5, R27.37).");
        }
        var built = Construct(loc, WellKnown.StructName(bw.Struct), bw.Struct, given);
        var structValue = built is IrNew n ? n with { Type = bw.StructType } : built;
        if (!extended) return new IrReturn(loc, structValue);
        if (tail.Count > 0)
        {
            const string selfLocal = BorrowContext.SelfCell;
            prefix.Add(new IrLocalDecl(loc, selfLocal, bw.StructType, structValue));
            var selfVar = new IrVar(loc, selfLocal) { Type = bw.StructType };
            foreach (var (callee, call) in tail)
                prefix.Add(new IrExprStmt(Locations.From(call),
                    BorrowingCall(callee, new IrRefArg(loc, selfVar),
                        call.ArgumentList.Arguments.Select(x => Lower(x.Expression)), Locations.From(call))));
            structValue = selfVar;
        }
        return new IrBlock(loc, [.. prefix, new IrReturn(loc, structValue)]);
    }

    private static bool ContainsCall(IrExpr e) => e switch
    {
        IrCall => true,
        IrField f => ContainsCall(f.Receiver),
        IrBinary b => ContainsCall(b.Left) || ContainsCall(b.Right),
        IrUnary u => ContainsCall(u.Operand),
        IrConvert c => ContainsCall(c.Operand),
        IrConditional c => ContainsCall(c.Cond) || ContainsCall(c.Then) || ContainsCall(c.Else),
        _ => false,
    };
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

    public static IEnumerable<IrExpr> Invariants(BorrowContext borrow, WellKnown known, IrLoc loc, bool snapshots = true)
    {
        var self = new IrVar(loc, borrow.SelfName) { Type = borrow.StructType };
        yield return new IrBinary(loc, BinOp.Eq,
            new IrField(loc, self, borrow.Owner.Name) { Type = borrow.OwnerType },
            new IrRefOf(loc, borrow.OwnerName) { Type = borrow.OwnerType }) { Type = IrPrim.Bool };
        // R27.37. Each owned field holds its parameter.
        foreach (var f in borrow.Owned)
            if (known.MapType(f.Type) is IrClassType ot)
                yield return new IrBinary(loc, BinOp.Eq, new IrField(loc, self, f.Name) { Type = ot },
                    new IrRefOf(loc, borrow.OwnedLocal(f)) { Type = ot }) { Type = IrPrim.Bool };
        if (!snapshots) yield break;
        foreach (var (f, type) in ReadOnlyFields(borrow, known))
        {
            var snapshotType = type.IsMachineInt ? new IrPrim(PrimKind.SpecInt) : type;
            yield return new IrBinary(loc, BinOp.Eq, new IrField(loc, self, f.Name) { Type = type },
                new IrVar(loc, Snapshot(f)) { Type = snapshotType }) { Type = IrPrim.Bool };
        }
    }
}
