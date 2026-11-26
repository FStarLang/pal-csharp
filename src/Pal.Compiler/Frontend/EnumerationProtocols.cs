using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using Pal.Compiler.Ir;
using System.Collections.Immutable;

namespace Pal.Compiler.Frontend;

/// <summary>
/// Nominal, monomorphic devirtualization of a freshly boxed borrowing enumerator.
/// No box identity/injectivity axiom is used: a forwarding body is inspected, and
/// only a nonescaping local's calls are specialized to the very struct it boxes.
/// </summary>
internal static class EnumerationProtocols
{
    private static bool CheckedMethod(IMethodSymbol method, WellKnown known) =>
        Declarations.KindOf(method, known) == CalleeKind.Method &&
        !Declarations.Has(method, known.AdmitAttribute) &&
        !Declarations.Has(method, known.ImplementsAttribute) &&
        !Declarations.Has(method, known.PulseBodyAttribute);

    internal sealed record Plan(IMethodSymbol Method, IMethodSymbol? GuardGetter = null,
        int GuardValue = 0, bool GuardEqual = false);
    internal static bool Same(ISymbol? a, ISymbol? b) =>
        a is not null && b is not null &&
        (SymbolEqualityComparer.Default.Equals(a, b) ||
         a.OriginalDefinition.DeclaringSyntaxReferences.Any(x =>
             b.OriginalDefinition.DeclaringSyntaxReferences.Any(y =>
                 x.SyntaxTree == y.SyntaxTree && x.Span == y.Span)) &&
         a.ContainingType is { } ac && b.ContainingType is { } bc &&
         EnumerableCasts.SameClass(ac, bc));

    internal static IMethodSymbol? Factory(INamedTypeSymbol source, ITypeSymbol element, WellKnown known) =>
        Resolve(source, element, known)?.Method;

    internal static IEnumerable<INamedTypeSymbol> Hierarchy(INamedTypeSymbol source)
    {
        for (var current = source; current is not null; current = current.BaseType)
            yield return current;
    }

    private static IMethodSymbol? Rebind(IMethodSymbol method, INamedTypeSymbol source) =>
        Hierarchy(source).SelectMany(t => t.GetMembers(method.Name).OfType<IMethodSymbol>())
            .FirstOrDefault(m => Same(m.OriginalDefinition, method.OriginalDefinition));

    internal static Plan? Resolve(INamedTypeSymbol source, ITypeSymbol element, WellKnown known)
    {
        var iface = source.AllInterfaces.FirstOrDefault(i =>
            i.OriginalDefinition.SpecialType == SpecialType.System_Collections_Generic_IEnumerable_T &&
            SymbolEqualityComparer.Default.Equals(i.TypeArguments[0], element));
        if (iface?.GetMembers("GetEnumerator").SingleOrDefault() is not IMethodSymbol slot ||
            NominalDispatch.InterfaceSlot(source, slot) is not { } implementation)
            return null;
        // A forwarding call, optionally guarded by a read-only integer property
        // comparison. The unselected branch is NEVER assumed empty: the adapter
        // must prove that execution selects this concrete factory.
        var syntax = implementation.DeclaringSyntaxReferences.FirstOrDefault()?.GetSyntax();
        var expression = syntax switch {
            MethodDeclarationSyntax { ExpressionBody.Expression: var e } => e,
            MethodDeclarationSyntax { Body.Statements: [ReturnStatementSyntax { Expression: var e }] } => e,
            _ => null
        };
        if (expression is null) return null;
        var model = known.Compilation.Model(expression.SyntaxTree);
        IMethodSymbol? guard = null;
        int guardValue = 0;
        bool guardEqual = false;
        if (expression is ConditionalExpressionSyntax conditional)
        {
            bool yes = IsFactoryCall(conditional.WhenTrue);
            if (yes == IsFactoryCall(conditional.WhenFalse) ||
                conditional.Condition is not BinaryExpressionSyntax condition ||
                condition.Kind() is not (SyntaxKind.EqualsExpression or SyntaxKind.NotEqualsExpression) ||
                condition.Left is not (IdentifierNameSyntax or MemberAccessExpressionSyntax { Expression: ThisExpressionSyntax }) ||
                model.GetSymbolInfo(condition.Left).Symbol is not IPropertySymbol {
                    IsStatic: false, Type.SpecialType: SpecialType.System_Int32, GetMethod: { } getter } ||
                !Declarations.IsReadOnly(getter, known.Compilation, known) ||
                model.GetConstantValue(condition.Right) is not { HasValue: true, Value: int n })
                return null;
            var declaration = Hierarchy(source)
                .SelectMany(t => t.GetMembers(getter.AssociatedSymbol!.Name).OfType<IPropertySymbol>())
                .FirstOrDefault(p => Same(p.GetMethod?.OriginalDefinition, getter.OriginalDefinition))?.GetMethod;
            guard = declaration is null ? null : NominalDispatch.ClassSlot(source, declaration);
            if (guard is null || !CheckedMethod(guard, known)) return null;
            guardValue = n;
            guardEqual = yes == condition.IsKind(SyntaxKind.EqualsExpression);
            expression = yes ? conditional.WhenTrue : conditional.WhenFalse;
        }
        if (expression is not InvocationExpressionSyntax { ArgumentList.Arguments.Count: 0 } call ||
            call.Expression is not (IdentifierNameSyntax or MemberAccessExpressionSyntax { Expression: ThisExpressionSyntax }))
            return null;
        if (model.GetSymbolInfo(call).Symbol is not IMethodSymbol {
                IsStatic: false, IsVirtual: false, Parameters.IsEmpty: true } factory ||
            !Hierarchy(source).Any(t => EnumerableCasts.SameClass(
                factory.ContainingType.OriginalDefinition, t.OriginalDefinition)) ||
            factory.ReturnType is not INamedTypeSymbol { TypeKind: TypeKind.Struct } st ||
            !Borrowing.IsBorrowing(st, known) ||
            model.GetDeclaredSymbol(syntax!) is not IMethodSymbol declared ||
            !model.Compilation.ClassifyConversion(factory.ReturnType, declared.ReturnType).IsBoxing ||
            !CheckedMethod(factory, known))
            return null;
        // Rebind the factory to the source's instantiated generic type.
        var method = Rebind(factory, source);
        return method is null ? null : new Plan(method, guard, guardValue, guardEqual);

        bool IsFactoryCall(ExpressionSyntax e) => e is InvocationExpressionSyntax invocation &&
            model.GetSymbolInfo(invocation).Symbol is IMethodSymbol {
                IsStatic: false, ReturnType: INamedTypeSymbol { TypeKind: TypeKind.Struct } result } &&
            Borrowing.IsBorrowing(result, known);
    }

    internal static (Plan Plan, ExpressionSyntax Receiver)? BoxedFactory(
        ExpressionSyntax expression, SemanticModel model, WellKnown known)
    {
        if (expression is not InvocationExpressionSyntax {
                Expression: MemberAccessExpressionSyntax { Expression: var receiver },
                ArgumentList.Arguments.Count: 0 } call ||
            model.GetSymbolInfo(call).Symbol is not IMethodSymbol slot ||
            slot.Name != "GetEnumerator" ||
            slot.ContainingType.OriginalDefinition.SpecialType != SpecialType.System_Collections_Generic_IEnumerable_T ||
            ExprLowerer.Unparenthesized(receiver) is not CastExpressionSyntax cast ||
            model.GetTypeInfo(cast.Type).Type is not INamedTypeSymbol iface ||
            !SymbolEqualityComparer.Default.Equals(iface, slot.ContainingType) ||
            model.GetTypeInfo(cast.Expression).Type is not INamedTypeSymbol { IsSealed: true } source ||
            Resolve(source, slot.ContainingType.TypeArguments[0], known) is not { } plan)
            return null;
        return (plan, ExprLowerer.Unparenthesized(cast.Expression));
    }

    // Evaluate the actual checked getter, then prove selection. This is a
    // proof obligation, not a runtime-filtering change to enumeration.
    internal static IEnumerable<IrStmt> Guard(Plan plan, ExprLowerer code, IrExpr receiver, string name, IrLoc loc)
    {
        if (plan.GuardGetter is not { } getter) yield break;
        yield return new IrLocalDecl(loc, name, IrPrim.Int, code.OwnerCall(getter, receiver, loc)) { Immutable = true };
        yield return new IrGhostStmt(loc, GhostKind.Assert,
            new IrBinary(loc, plan.GuardEqual ? BinOp.Eq : BinOp.Ne,
                new IrVar(loc, name) { Type = IrPrim.Int },
                new IrLiteral(loc, plan.GuardValue) { Type = IrPrim.Int }) { Type = IrPrim.Bool }, null);
    }

    internal static ISymbol? Implementation(INamedTypeSymbol st, ISymbol slot) =>
        slot.ContainingType?.TypeKind == TypeKind.Interface
            ? st.FindImplementationForInterfaceMember(slot) : slot;

    // These are obligations on the actual nominal methods, NOT axioms or claims
    // read off user contract text. Borrowing lowering checks the union of the
    // authored and protocol domains, guarding each postcondition by its own
    // old precondition. Neither stale-version exceptions nor partial disposal
    // may be hidden by restricting verification to the other domain.
    internal static ImmutableArray<(bool Post, string Text)> Laws(IMethodSymbol method, WellKnown known)
    {
        var st = method.ContainingType;
        var annotation = st.GetAttributes().SingleOrDefault(a =>
            SymbolEqualityComparer.Default.Equals(a.AttributeClass, known.EnumerationStateAttribute));
        var interfaces = st.AllInterfaces.Where(i => i.OriginalDefinition.ToDisplayString() ==
            "System.Collections.Generic.IEnumerator<T>").ToArray();
        if (annotation is null || !Borrowing.IsBorrowing(st, known) ||
            interfaces.Length != 1)
            return [];
        var iface = interfaces[0];
        var names = Enumerable.Range(0, 4).Select(i => Declarations.StringArgument(annotation, i)).ToArray();
        var props = names.Select(n => n is not null && SyntaxFacts.IsValidIdentifier(n)
            ? st.GetMembers(n).OfType<IPropertySymbol>().SingleOrDefault() : null).ToArray();
        if (props.Any(p => p is null || p.IsStatic || !Declarations.Has(p, known.SpecAttribute)) ||
            props[0]!.Type.SpecialType != SpecialType.System_Boolean ||
            props[3]!.Type.SpecialType != SpecialType.System_Boolean ||
            known.MapType(props[1]!.Type) is not IrSeqType remaining ||
            !Equals(remaining.Element, known.MapType(iface.TypeArguments[0])))
            return [];
        var scalarCurrent = SymbolEqualityComparer.Default.Equals(props[2]!.Type, iface.TypeArguments[0]);
        var sequenceCurrent = known.MapType(props[2]!.Type) is IrSeqType current &&
            current.Element.Equals(remaining.Element);
        if (!scalarCurrent && !sequenceCurrent) return [];
        string ready = $"@this.{names[0]}", rest = $"@this.{names[1]}",
            value = $"@this.{names[2]}", valid = $"@this.{names[3]}";
        string old = $"PalLang.Pal.Old({rest})";
        string currentValue = sequenceCurrent ? $"{value}[0]" : value;
        bool IsSlot(string type, string member) =>
            st.AllInterfaces.FirstOrDefault(i => i.OriginalDefinition.ToDisplayString() == type)?
                .GetMembers(member).Any(s => Same(st.FindImplementationForInterfaceMember(s),
                    method.AssociatedSymbol ?? (ISymbol)method)) == true;
        if (IsSlot("System.Collections.IEnumerator", "MoveNext"))
            return [
                (false, ready),
                (true, ready),
                (true, $"Result == ({old}.Length > 0)"),
                (true, $"{rest}.Length == {old}.Length - (Result ? 1 : 0)"),
                (true, $"PalLang.Pal.Forall((PalLang.SpecInt i) => PalLang.Pal.Implies(0 <= i && i < {rest}.Length, PalLang.Pal.Same({rest}[i], {old}[i + (Result ? 1 : 0)])))"),
                (true, $"PalLang.Pal.Implies(Result, {valid} && " +
                    (sequenceCurrent ? $"{value}.Length == 1 && " : "") +
                    $"PalLang.Pal.Same({currentValue}, {old}[0]))"),
                .. (sequenceCurrent ? new (bool Post, string Text)[] {
                    (true, $"PalLang.Pal.Implies(!Result, {value}.Length == 0)"),
                    (true, $"{valid} == Result")
                } : [])
            ];
        ImmutableArray<(bool Post, string Text)> Preserves() => [
                (true, ready),
                (true, $"{rest}.Length == {old}.Length"),
                (true, $"PalLang.Pal.Forall((PalLang.SpecInt i) => PalLang.Pal.Implies(0 <= i && i < {rest}.Length, PalLang.Pal.Same({rest}[i], {old}[i])))"),
                (true, $"{valid} == PalLang.Pal.Old({valid})"),
                .. (sequenceCurrent ? new (bool Post, string Text)[] {
                    (true, $"{value}.Length == PalLang.Pal.Old({value}).Length"),
                    (true, $"PalLang.Pal.Forall((PalLang.SpecInt i) => PalLang.Pal.Implies(0 <= i && i < {value}.Length, PalLang.Pal.Same({value}[i], PalLang.Pal.Old({value})[i])))")
                } : [(true, $"PalLang.Pal.Implies({valid}, PalLang.Pal.Same({value}, PalLang.Pal.Old({value})))")])
            ];
        if (IsSlot("System.Collections.Generic.IEnumerator<T>", "Current"))
            return [(false, $"{ready} && {valid}" + (sequenceCurrent ? $" && {value}.Length == 1" : "")),
                (true, $"PalLang.Pal.Same(Result, {currentValue})"), .. Preserves()];
        if (IsSlot("System.IDisposable", "Dispose"))
            return [(false, ready), .. Preserves()];
        return [];
    }

    internal static bool HasLaws(INamedTypeSymbol st, WellKnown known)
    {
        IMethodSymbol? Slot(string type, string name) =>
            st.AllInterfaces.FirstOrDefault(i => i.OriginalDefinition.ToDisplayString() == type)?
                .GetMembers(name).Select(s => st.FindImplementationForInterfaceMember(s))
                .Select(s => s is IPropertySymbol p ? p.GetMethod : s as IMethodSymbol).SingleOrDefault();
        var current = Slot("System.Collections.Generic.IEnumerator<T>", "Current");
        var methods = new[] { Slot("System.Collections.IEnumerator", "MoveNext"), current,
            Slot("System.IDisposable", "Dispose") };
        return methods.All(m => m is not null && !Laws(m, known).IsEmpty &&
                CheckedMethod(m, known)) &&
            current?.DeclaringSyntaxReferences.FirstOrDefault()?.GetSyntax() is { } syntax &&
            !Borrowing.WritesState(syntax, known.Compilation.Model(syntax.SyntaxTree), st);
    }

    internal static IrIterationSchema? Schema(INamedTypeSymbol source, ITypeSymbol element, WellKnown known)
    {
        if (Factory(source, element, known) is not { ReturnType: INamedTypeSymbol st } factory ||
            !HasLaws(st, known) ||
            !st.AllInterfaces.Any(i => i.OriginalDefinition.ToDisplayString() ==
                "System.Collections.Generic.IEnumerator<T>" &&
                SymbolEqualityComparer.Default.Equals(i.TypeArguments[0], element)))
            return null;
        var annotation = st.GetAttributes().Single(a =>
            SymbolEqualityComparer.Default.Equals(a.AttributeClass, known.EnumerationStateAttribute));
        var names = Enumerable.Range(0, 4).Select(i => Declarations.StringArgument(annotation, i)!).ToArray();
        // The dynamic ABI uses an optional sequence, so it needs no default(T).
        if (known.MapType(st.GetMembers(names[2]).OfType<IPropertySymbol>().Single().Type)
            is not IrSeqType)
            return null;
        return new(factory.Name, names[0], names[1], names[2], names[3]) {
            Evidence = Evidence(source, element, known) is { } witness ? Naming.Of(witness) : null
        };
    }

    internal static IMethodSymbol? Evidence(INamedTypeSymbol source, ITypeSymbol element, WellKnown known)
        => Evidence(source, element, known, out _);

    internal static IMethodSymbol? Evidence(INamedTypeSymbol source, ITypeSymbol element, WellKnown known,
        out string reason)
    {
        reason = "marked traversal, resolved factory, or checked state laws do not match";
        var marked = Hierarchy(source).SelectMany(t => t.GetMembers().OfType<IMethodSymbol>())
            .Where(m => Declarations.Has(m, known.EnumerationProtocolAttribute)).ToArray();
        if (marked.Length != 1 || marked[0] is not { IsStatic: false, Parameters.IsEmpty: true } witness ||
            !CheckedMethod(witness, known) ||
            !SymbolEqualityComparer.Default.Equals(Iterators.Element(witness), element) ||
            Factory(source, element, known) is not { ReturnType: INamedTypeSymbol st } factory ||
            !HasLaws(st, known) ||
            !st.AllInterfaces.Any(i => i.OriginalDefinition.ToDisplayString() ==
                "System.Collections.Generic.IEnumerator<T>" &&
                SymbolEqualityComparer.Default.Equals(i.TypeArguments[0], element)) ||
            witness.DeclaringSyntaxReferences.FirstOrDefault()?.GetSyntax() is not MethodDeclarationSyntax {
                Body: { } witnessBody })
            return null;
        var model = known.Compilation.Model(witnessBody.SyntaxTree);
        var top = Runtime(witnessBody);
        reason = "unrecognized top-level traversal after erasing proof statements";
        if (top.Length is not (3 or 4) ||
            top[0] is not LocalDeclarationStatementSyntax {
                UsingKeyword.RawKind: 0, Declaration.Variables: [var local] } ||
            top[^2] is not WhileStatementSyntax { Statement: BlockSyntax body } loop ||
            top[^1] is not ExpressionStatementSyntax finish)
            return null;
        reason = "factory or disposal call does not match the resolved iterator";
        if (local.Initializer?.Value is not InvocationExpressionSyntax init ||
            model.GetSymbolInfo(init).Symbol is not IMethodSymbol actual ||
            !Same(actual.OriginalDefinition, factory.OriginalDefinition) ||
            init.ArgumentList.Arguments.Count != 0 ||
            init.Expression is not (IdentifierNameSyntax or MemberAccessExpressionSyntax { Expression: ThisExpressionSyntax }) ||
            model.GetDeclaredSymbol(local) is not ILocalSymbol variable ||
            !Call(finish.Expression, "System.IDisposable", "Dispose"))
            return null;
        var runtime = Runtime(body);
        reason = "unrecognized traversal loop after erasing proof statements";
        if (top.Length == 3)
        {
            if (!Call(loop.Condition, "System.Collections.IEnumerator", "MoveNext") ||
                runtime is not [YieldStatementSyntax yield] || !Yield(yield))
                return null;
        }
        else
        {
            // Equivalent explicit-state spelling:
            // bool more = true; while(more) { more = e.MoveNext(); if(more) yield e.Current; }
            // Only erased proof statements may intervene. No extra calls, exits,
            // writes, or cursor aliases can change the observed traversal.
            if (top[1] is not LocalDeclarationStatementSyntax { UsingKeyword.RawKind: 0,
                    Declaration.Variables: [var flag] } ||
                flag.Initializer?.Value is not LiteralExpressionSyntax initial ||
                !initial.IsKind(SyntaxKind.TrueLiteralExpression) ||
                model.GetDeclaredSymbol(flag) is not ILocalSymbol {
                    Type.SpecialType: SpecialType.System_Boolean } more ||
                !Same(model.GetSymbolInfo(loop.Condition).Symbol, more) ||
                runtime is not [
                    ExpressionStatementSyntax { Expression: AssignmentExpressionSyntax assignment },
                    IfStatementSyntax { Statement: BlockSyntax yes, Else: null } branch] ||
                !assignment.IsKind(SyntaxKind.SimpleAssignmentExpression) ||
                !Same(model.GetSymbolInfo(assignment.Left).Symbol, more) ||
                !Call(assignment.Right, "System.Collections.IEnumerator", "MoveNext") ||
                !Same(model.GetSymbolInfo(branch.Condition).Symbol, more) ||
                Runtime(yes) is not [YieldStatementSyntax yield] || !Yield(yield))
                return null;
        }
        reason = "";
        return witness;

        StatementSyntax[] Runtime(BlockSyntax block) =>
            block.Statements.Where(s => !Proof(s)).ToArray();
        bool Proof(StatementSyntax statement)
        {
            if (statement is LocalDeclarationStatementSyntax { Declaration.Variables: [var ghost] } &&
                model.GetDeclaredSymbol(ghost) is ILocalSymbol g && known.IsGhost(g.Type) &&
                ghost.Initializer?.Value is LiteralExpressionSyntax d && d.IsKind(SyntaxKind.DefaultLiteralExpression))
                return true;
            return statement is ExpressionStatementSyntax { Expression: InvocationExpressionSyntax proof } &&
                model.GetSymbolInfo(proof).Symbol is IMethodSymbol intrinsic &&
                (known.IsPalIntrinsic(intrinsic) &&
                    intrinsic.Name is ("Invariant" or "Decreases" or "Assert" or "Join" or "Capture") ||
                    Declarations.KindOf(intrinsic, known) == CalleeKind.Lemma ||
                    intrinsic.ReturnsVoid && known.SpecOpName(intrinsic) is not null &&
                    intrinsic.GetAttributes().Any(a =>
                        a.AttributeClass?.ToDisplayString() == "System.Diagnostics.ConditionalAttribute" &&
                        Declarations.StringArgument(a, 0) == "PAL"));
        }
        bool Yield(YieldStatementSyntax yield) =>
            yield.IsKind(SyntaxKind.YieldReturnStatement) &&
            yield.Expression is MemberAccessExpressionSyntax current && OnLocal(current.Expression) &&
            Slot(current, "System.Collections.Generic.IEnumerator<T>", "Current");
        bool OnLocal(ExpressionSyntax e) => Same(model.GetSymbolInfo(e).Symbol, variable);
        bool Slot(ExpressionSyntax e, string iface, string name) =>
            ((INamedTypeSymbol)actual.ReturnType).AllInterfaces.FirstOrDefault(i => i.OriginalDefinition.ToDisplayString() == iface)?
                .GetMembers(name).Any(s => Same(((INamedTypeSymbol)actual.ReturnType).FindImplementationForInterfaceMember(s), model.GetSymbolInfo(e).Symbol)) == true;
        bool Call(ExpressionSyntax e, string iface, string name) =>
            e is InvocationExpressionSyntax { Expression: MemberAccessExpressionSyntax access, ArgumentList.Arguments.Count: 0 } &&
            OnLocal(access.Expression) && Slot(e, iface, name);
    }
}
