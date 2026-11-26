using System.Collections.Immutable;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using Pal.Compiler.Ir;

namespace Pal.Compiler.Frontend;

public sealed partial class ExprLowerer
{
    // Scoped only while lowering the successful class-test branch. This is NOT
    // an ordinary class reference and must never flow to an ordinary helper ABI.
    internal readonly Dictionary<string, IrVar> NominalCaptures =
        known.Specialization?.NominalParameters.ToDictionary(kv => kv.Key,
            kv => new IrVar(IrLoc.None, kv.Key) { Type = kv.Value }) ?? [];

    private bool _nominalArgumentLowering;

    /// <summary>
    /// Re-verify a private self helper with capability parameters, including its
    /// original contracts. Neither the caller nor the specialized body obtains
    /// a fabricated ordinary class invariant. Virtual receiver calls inside the
    /// helper still use the caller's ordinary or borrowed-view representation.
    /// </summary>
    private IrExpr? NominalHelperCall(InvocationExpressionSyntax node, IMethodSymbol method, IrLoc loc)
    {
        if (_nominalArgumentLowering || SpecPosition) return null;
        if (node.Expression is MemberAccessExpressionSyntax { Expression: IdentifierNameSyntax receiver } &&
            NominalCaptures.ContainsKey(receiver.Identifier.ValueText))
        {
            diagnostics.Error("PALCS0866", loc,
                $"`{method.Name}` on a retained nominal receiver requires an installed method/iterator slot; " +
                "the observation capability cannot be reinterpreted as an ordinary class pointer.");
            return new IrLiteral(loc, null);
        }
        var args = node.ArgumentList.Arguments;
        var captured = args.Select(a => Unparenthesized(a.Expression) is IdentifierNameSyntax id &&
            NominalCaptures.TryGetValue(id.Identifier.ValueText, out var source) ? source : null).ToArray();
        if (captured.All(s => s is null)) return null;
        IrExpr Refuse()
        {
            diagnostics.Error("PALCS0866", loc,
                "A retained nominal value can be passed only to a translated private nonvirtual self helper " +
                "whose concrete parameters are all retained capabilities. Its body and contracts are re-verified at that ABI.");
            return new IrLiteral(loc, null);
        }
        if (method.IsStatic || method.IsVirtual || method.IsOverride || method.IsAbstract ||
            method.DeclaredAccessibility != Accessibility.Private || method.IsGenericMethod ||
            method.MethodKind != MethodKind.Ordinary ||
            node.Expression is not IdentifierNameSyntax &&
                node.Expression is not MemberAccessExpressionSyntax { Expression: ThisExpressionSyntax } ||
            Declarations.KindOf(method, known) != CalleeKind.Method ||
            Declarations.Has(method, known.AdmitAttribute) ||
            Declarations.Has(method, known.ImplementsAttribute) ||
            Declarations.Has(method, known.PulseBodyAttribute) ||
            args.Count != method.Parameters.Length ||
            captured.Any(s => s is null) ||
            method.Parameters.Any(p => p.RefKind != RefKind.None || known.IsGhost(p.Type) ||
                Declarations.Has(p, known.ConsumesAttribute) || Declarations.Has(p, known.ExactlyAttribute)) ||
            method.DeclaringSyntaxReferences.IsEmpty ||
            model.GetEnclosingSymbol(node.SpanStart) is not IMethodSymbol caller ||
            !(SymbolEqualityComparer.Default.Equals(caller.ContainingType.OriginalDefinition,
                method.ContainingType.OriginalDefinition) ||
              Borrow is { ViewBase: { } viewBase } &&
              SymbolEqualityComparer.Default.Equals(viewBase.OriginalDefinition, method.ContainingType.OriginalDefinition)))
            return Refuse();
        var parameters = ImmutableDictionary.CreateBuilder<string, IrEnumerableType>(StringComparer.Ordinal);
        for (var i = 0; i < captured.Length; i++)
        {
            if (captured[i]!.Type is not IrEnumerableType { Capability: not null, CastTarget: { } target } e ||
                known.MapType(method.Parameters[i].Type) is not IrClassType declared ||
                declared.Nullable || target.Name != declared.Name ||
                !target.TypeArguments.SequenceEqual(declared.TypeArguments))
                return Refuse();
            parameters.Add(method.Parameters[i].Name, e);
        }
        // Let the ordinary lowering select the receiver and borrowed-view ABI.
        // Only the already checked argument positions may lower as capabilities.
        IrExpr lowered;
        _nominalArgumentLowering = true;
        try { lowered = LowerInvocation(node, loc); }
        finally { _nominalArgumentLowering = false; }
        if (lowered is not IrCall call) return Refuse();
        var sourceName = Naming.Of(method.OriginalDefinition);
        var name = call.Callee + "__nominal_" + string.Join("_", method.Parameters.Select(p => p.Name));
        var replica = Borrow is { Constructor: false, ViewBase: not null } bw
            ? new WellKnown.ReplicaRequest(sourceName, bw.Struct.OriginalDefinition, name) : null;
        if (known.SpecializationSeen.Add(name))
            known.SpecializationDemand.Enqueue(new WellKnown.SpecializationRequest(sourceName, name,
                ImmutableDictionary<string, bool>.Empty) {
                At = loc, Replica = replica, NominalParameters = parameters.ToImmutable()
            });
        // Lower normally restores each expression's C# static type. These last
        // arguments instead use the checked capability ABI, never that class type.
        call = call with { Args = [.. call.Args.Take(call.Args.Length - captured.Length),
            .. captured.Select(s => (IrExpr)s!)] };
        return call with { Callee = name,
            ParamTypes = [.. call.Args.Select((a, i) => a.Type is IrEnumerableType { Capability: not null }
                ? a.Type : i < call.ParamTypes.Length ? call.ParamTypes[i] : null)]
        };
    }

    private IrExpr? NominalMember(MemberAccessExpressionSyntax node, ISymbol? symbol, IrLoc loc)
    {
        var receiver = Unparenthesized(node.Expression);
        IrVar? source = receiver is IdentifierNameSyntax id &&
            NominalCaptures.TryGetValue(id.Identifier.ValueText, out var captured) ? captured : null;
        // Logical casts in contracts observe the same retained descriptor model;
        // they do not reinterpret its contents sequence as a concrete class model.
        if (source is null && SpecPosition && receiver is CastExpressionSyntax cast &&
            Unparenthesized(cast.Expression) is IdentifierNameSyntax input &&
            CastParameters.TryGetValue(input.Identifier.ValueText, out var parameter) &&
            parameter.CastTarget is { } target &&
            model.GetTypeInfo(cast.Type).Type is { } castType &&
            known.MapType(castType) is IrClassType ct && ct.Name == target.Name &&
            ct.TypeArguments.SequenceEqual(target.TypeArguments))
            source = new IrVar(loc, input.Identifier.ValueText) { Type = parameter };
        if (source is null ||
            source.Type is not IrEnumerableType { Capability: { } schema } e) return null;
        if (symbol is IPropertySymbol p)
        {
            if (p.Name == schema.LengthGetter || p.Name == schema.ScalarGetter)
                return new IrEnumOp(loc, EnumOpKind.Observation, source, []) {
                    ScalarObservation = p.Name == schema.ScalarGetter,
                    Type = p.Name == schema.ScalarGetter ? schema.ScalarType : IrPrim.Int };
            if (SpecPosition && (p.Name == schema.Items || p.Name == schema.Scalar))
                return new IrSpecOp(loc, p.Name == schema.Items
                    ? "enum_contents_" + source.Name
                    : "enum_scalar_" + source.Name,
                    [new IrVar(loc, "$nominal:" + source.Name)])
                    { Type = p.Name == schema.Items ? new IrSeqType(e.Element) : schema.ScalarType };
        }
        diagnostics.Error("PALCS0866", loc,
            "This nominal capability exposes only its installed length/scalar observations. " +
            "Concrete helpers, fields and iterator slots need a separate capability ABI.");
        return new IrLiteral(loc, null);
    }

    private INamedTypeSymbol? NominalExact(ExpressionSyntax expression)
    {
        if (ExactClassOf(expression) is { } exact) return exact;
        if (model.GetTypeInfo(expression).Type is INamedTypeSymbol { IsSealed: true } sealedClass)
            return sealedClass;
        // A fresh allocation is exact, but a mutable alias is not. Reject all
        // assignments/ref escapes, including ones after this call, conservatively.
        if (model.GetSymbolInfo(expression).Symbol is not ILocalSymbol local ||
            local.DeclaringSyntaxReferences.SingleOrDefault()?.GetSyntax() is not VariableDeclaratorSyntax {
                Initializer.Value: ObjectCreationExpressionSyntax creation } declaration ||
            creation.Initializer is not null)
            return null;
        var body = declaration.Ancestors().OfType<BaseMethodDeclarationSyntax>().FirstOrDefault();
        if (body is null || body.DescendantNodes().OfType<IdentifierNameSyntax>().Any(n =>
            SymbolEqualityComparer.Default.Equals(model.GetSymbolInfo(n).Symbol, local) &&
            n.Ancestors().TakeWhile(a => a != body).Any(a =>
                a is AssignmentExpressionSyntax assignment && assignment.Left.Span.Contains(n.Span) ||
                a is ArgumentSyntax arg && arg.RefKindKeyword.RawKind != 0 ||
                a is RefExpressionSyntax)))
            return null;
        return model.GetTypeInfo(creation).Type as INamedTypeSymbol;
    }

    private IrExpr NominalSnapshot(ArgumentSyntax argument, IParameterSymbol parameter, IrEnumerableType e)
    {
        var loc = Locations.From(argument);
        IrExpr Refuse(string reason)
        {
            diagnostics.Error("PALCS0866", loc, "Nominal enumerable installation: " + reason);
            return new IrLiteral(loc, null);
        }
        var held = BorrowingView(argument.Expression);
        var exact = held?.Struct ?? NominalExact(argument.Expression);
        var target = EnumerableCasts.Target(parameter, known)!;
        if (exact is null) return Refuse("the runtime source class is unknown; a nonsealed static type is not exact evidence.");
        var hit = NominalDispatch.Assignable(exact, target);
        if (hit is null) return Refuse("generic runtime assignability is unknown.");
        if (hit == false)
            return held is null ? NominalMissSnapshot(argument, parameter, e, exact)
                : Refuse("disjoint borrowed-view source ownership is not installed.");
        if (held is null && (!EnumerableCasts.SameClass(exact, target) ||
            known.MapType(exact) is not IrClassType { Nullable: false }))
            return Refuse("this source has no supported ordinary or retained-view ownership representation.");
        if (held is not null && (!exact.IsSealed || held.OwnerView is not null ||
            !held.Owned.IsEmpty || !held.CorePath.IsEmpty || held.StructType is not IrNamedType))
            return Refuse("the view must be a sealed, direct borrowed-owner record without additional owned resources.");
        var schema = e.Capability!;
        IMethodSymbol? Slot(string name) => target.GetMembers(name).OfType<IPropertySymbol>()
            .SingleOrDefault()?.GetMethod is { } g ? NominalDispatch.ClassSlot(exact, g) : null;
        var length = Slot(schema.LengthGetter);
        var scalar = Slot(schema.ScalarGetter);
        bool Checked(IMethodSymbol? m) => m is not null &&
            Declarations.KindOf(m, known) == CalleeKind.Method &&
            !Declarations.Has(m, known.AdmitAttribute) &&
            !Declarations.Has(m, known.ImplementsAttribute) &&
            !Declarations.Has(m, known.PulseBodyAttribute);
        if (!Checked(length) || !Checked(scalar) ||
            EnumerationObservations.Resolve(length!, known) is null ||
            EnumerationObservations.Resolve(scalar!, known) is null)
            return Refuse("actual class slots must be checked annotated observation getters.");
        var element = ((INamedTypeSymbol)parameter.Type).TypeArguments[0];
        var iface = exact.AllInterfaces.SingleOrDefault(i =>
            i.OriginalDefinition.SpecialType == SpecialType.System_Collections_Generic_IEnumerable_T &&
            SymbolEqualityComparer.Default.Equals(i.TypeArguments[0], element));
        var iterator = iface?.GetMembers("GetEnumerator").SingleOrDefault() is { } interfaceSlot
            ? NominalDispatch.InterfaceSlot(exact, interfaceSlot) : null;
        var protocolEvidence = EnumerationProtocols.Evidence(exact, element, known, out var evidenceFailure);
        var enumeration = iterator is not null && Iterators.Element(iterator) is not null
            ? iterator : protocolEvidence;
        var copyDeclaration = EnumerationProtocols.Hierarchy(exact)
            .SelectMany(c => c.GetMembers("CopyTo").OfType<IMethodSymbol>()).FirstOrDefault(m =>
            !m.IsStatic && m.Parameters is [{ Type: IArrayTypeSymbol array }, { Type.SpecialType: SpecialType.System_Int32 }] &&
            array.Rank == 1 && SymbolEqualityComparer.Default.Equals(array.ElementType, element));
        var copy = copyDeclaration is null ? null : NominalDispatch.ClassSlot(exact, copyDeclaration);
        if (!Checked(enumeration))
            return Refuse("the actual interface traversal has no recognized checked enumeration evidence: " + evidenceFailure + ".");
        if (!Checked(copy))
            return Refuse("the actual CopyTo slot is missing or unchecked.");
        if (!Declarations.IsReadOnly(enumeration!, model.Compilation, known))
            return Refuse("the checked enumeration evidence mutates the retained source.");
        if (!Declarations.IsReadOnly(copy!, model.Compilation, known))
            return Refuse("the actual CopyTo slot mutates the retained source.");
        if (held is null && (!Declarations.IsReadOnly(length!, model.Compilation, known) ||
            !Declarations.IsReadOnly(scalar!, model.Compilation, known)))
            return Refuse("the actual observation getters mutate the retained source.");
        if (e.Collection) return Refuse("collection-interface capabilities are outside this schema.");
        var owner = held is null ? Lower(argument.Expression) :
            new IrVar(loc, held.OwnerName) { Type = held.OwnerType };
        if (owner is not IrVar { Type: IrClassType ownerType })
            return Refuse("requires a named nonnullable retained owner.");
        ownerType = ownerType with { Nullable = false };
        owner = ((IrVar)owner) with { Type = ownerType };
        IrCall Call(IMethodSymbol method, IrExpr[] args)
        {
            if (held is not null)
                return (IrCall)WithHeld(held, () => HeldCall(held, method, args, loc));
            return new IrCall(loc, Naming.Of(method), [owner, .. args]) {
                Kind = CalleeKind.Method, ResultType = known.MapReturnType(method.ReturnType),
                HasReceiver = true, KeepsArguments = true,
                ParamTypes = Declarations.ParamTypes(method, known, true),
                TypeArguments = known.TypeArguments(method), MutatesReceiver = false };
        }
        var canonical = held is null ? null : held with { OwnerName = "owner", SelfName = "view" };
        IrExpr? Projection(IMethodSymbol getter)
        {
            var observation = EnumerationObservations.Resolve(getter, known)!.Observation;
            if (canonical is not null && ViewOverride(canonical.Struct, observation) is { } overridden)
                observation = overridden;
            return canonical is not null ? InlineSpec(canonical, observation, loc) :
                new IrObserve(loc, ownerType.Name, observation.Name,
                    new IrVar(loc, "owner") { Type = ownerType }) { Type = known.MapType(observation.Type) };
        }
        var items = Projection(length!);
        var value = Projection(scalar!);
        if (items is null || value is null) return Refuse("the actual spec projections could not be lowered.");
        var name = Fresh("nominal_snapshot");
        foreach (var tp in WellKnown.DefaultedIn(element)) DefaultedTypeParameters.Add(tp.Name);
        var arrayType = new IrArrayType(e.Element);
        var array = new IrVar(loc, name) { Type = arrayType };
        var seqType = new IrSeqType(e.Element);
        var yielded = Fresh("nominal_yielded");
        var lengthCall = Call(length!, []) with { ResultType = IrPrim.Int };
        var scalarCall = Call(scalar!, []);
        IrEnumerationCursor? cursor = null;
        if (schema.Iteration is { } protocol)
        {
            if (EnumerationProtocols.Factory(exact, element, known) is not {
                    ReturnType: INamedTypeSymbol st } factory ||
                EnumerationProtocols.Schema(exact, element, known) is null ||
                Borrowing.OwnerField(st, known) is not { } ownerField ||
                (canonical is null ? known.MapType(st) :
                    BorrowedOwners.Type(st, canonical.Struct, known)) is not IrNamedType cursorType)
                return Refuse("the successful runtime source needs a checked, resource-producing iterator protocol.");
            var owned = Borrowing.OwnedFields(st, known);
            if (owned.Any(f => known.MapType(f.Type) is not IrClassType { Nullable: false }))
                return Refuse("iterator-owned storage must have a nonnullable concrete class invariant.");
            var iteratorContext = new BorrowContext(st, ownerField, cursorType, ownerType, false, null) {
                SelfName = "cursor", OwnerName = "owner", OwnerView = canonical, Owned = owned,
                OwnedNames = owned.ToImmutableDictionary(f => f.Name, f => "aux" + f.Name)
            };
            IMethodSymbol IteratorSlot(string ifaceName, string member) =>
                st.AllInterfaces.Single(i => i.OriginalDefinition.ToDisplayString() == ifaceName)
                    .GetMembers(member).Select(m => st.FindImplementationForInterfaceMember(m))
                    .Select(m => m is IPropertySymbol p ? p.GetMethod! : (IMethodSymbol)m!).Single();
            IrExpr? State(string property) =>
                InlineSpec(iteratorContext, st.GetMembers(property).OfType<IPropertySymbol>().Single(), loc);
            IrCall Invoke(IMethodSymbol m) => (IrCall)WithHeld(iteratorContext,
                () => HeldCall(iteratorContext, m, [], loc));
            if (State(protocol.Ready) is not { } ready || State(protocol.Pending) is not { } pending ||
                State(protocol.CurrentItems) is not { } current || State(protocol.Valid) is not { } valid)
                return Refuse("the concrete iterator state observations could not be lowered.");
            cursor = new(cursorType, ownerField.Name, ready, pending, current, valid,
                Call(factory, []), Invoke(IteratorSlot("System.Collections.IEnumerator", "MoveNext")),
                Invoke(IteratorSlot("System.Collections.Generic.IEnumerator<T>", "Current")),
                Invoke(IteratorSlot("System.IDisposable", "Dispose")),
                [.. owned.Select(f => (f.Name, iteratorContext.OwnedLocal(f), (IrClassType)known.MapType(f.Type)!))]) {
                SpecTypes = WellKnown.AllTypeParameters(st).Select(t => t.Name)
                    .Zip(known.TypeArguments(st.GetMembers(protocol.Ready).OfType<IPropertySymbol>().Single().GetMethod!))
                    .ToImmutableDictionary(pair => pair.First, pair => pair.Second)
            };
        }
        var installation = new IrEnumerationInstallation("Nominal_" + LiftPrefix + "_" + name,
            LiftTypeParameters, e, ownerType, held?.StructType as IrNamedType, held?.Owner.Name,
            items, value, lengthCall.Callee, scalarCall.Callee,
            lengthCall.TypeArguments, scalarCall.TypeArguments) {
                Cursor = cursor,
                DefaultedTypes = [.. WellKnown.DefaultedIn(element).Select(t => t.Name)]
            };
        var setup = new List<IrStmt>();
        // Snapshot construction is instrumentation, not an extra observable
        // view mutation. Count may update the exclusive cache cell. Keep its
        // original record value and restore it before installing the descriptor;
        // the actual consumer's getter then performs the C# mutation. This is a
        // value copy, not a second owned view, and additional owned fields were
        // excluded above. The retained owner is preserved by all three calls.
        var savedView = held is null ? null : Fresh("snapshot_view_state");
        if (held is not null)
            setup.Add(new IrLocalDecl(loc, savedView!, held.StructType,
                new IrVar(loc, held.SelfName) { Type = held.StructType }) { Immutable = true });
        setup.AddRange([
            new IrLocalDecl(loc, name, arrayType, new IrNewArray(loc, e.Element, lengthCall) { Type = arrayType }),
            new IrExprStmt(loc, Call(copy!, [array, new IrLiteral(loc, 0) { Type = IrPrim.Int }])),
            new IrLocalDecl(loc, yielded, seqType, Call(enumeration!, []) with { ResultType = seqType })
        ]);
        if (held is not null)
            setup.Add(new IrAssign(loc, new IrVar(loc, held.SelfName) { Type = held.StructType },
                new IrVar(loc, savedView!) { Type = held.StructType }));
        return new IrStmtExpr(loc, setup.ToImmutableArray(), new IrEnumOp(loc, EnumOpKind.Lend, array,
            held is null ? [owner, new IrVar(loc, yielded) { Type = seqType }] :
                [owner, new IrVar(loc, yielded) { Type = seqType },
                 new IrRefOf(loc, held.SelfName) { Type = held.StructType }]) {
            Type = e, CastMatch = true, Installation = installation
        }) { Type = e };
    }

    // A nominal miss still owns the actual source and proves that the snapshot
    // agrees with its actual interface enumeration. No target-class slots are
    // manufactured, and a failure to resolve evidence is not a failed cast.
    private IrExpr NominalMissSnapshot(ArgumentSyntax argument, IParameterSymbol parameter,
        IrEnumerableType e, INamedTypeSymbol exact)
    {
        var loc = Locations.From(argument);
        IrExpr Refuse(string reason)
        {
            diagnostics.Error("PALCS0866", loc, "Disjoint nominal enumerable installation: " + reason);
            return new IrLiteral(loc, null);
        }
        if (!known.HasModel(exact) ||
            Lower(argument.Expression) is not IrVar { Type: IrClassType ownerType } owner)
            return Refuse("requires a named exact source with ordinary model ownership.");
        ownerType = ownerType with { Nullable = false };
        owner = owner with { Type = ownerType };
        var element = ((INamedTypeSymbol)parameter.Type).TypeArguments[0];
        var projections = exact.GetMembers().OfType<IPropertySymbol>()
            .Where(p => Declarations.Has(p, known.EnumerationModelAttribute)).ToArray();
        if (projections is not [{ IsStatic: false, Parameters.IsEmpty: true } projection] ||
            !Declarations.Has(projection, known.SpecAttribute) ||
            known.MapType(projection.Type) is not IrSeqType sequence || !sequence.Element.Equals(e.Element))
            return Refuse("requires exactly one [Spec, EnumerationModel] sequence of the element type.");
        bool Checked(IMethodSymbol? m) => m is not null &&
            Declarations.KindOf(m, known) == CalleeKind.Method &&
            !Declarations.Has(m, known.AdmitAttribute) &&
            !Declarations.Has(m, known.ImplementsAttribute) &&
            !Declarations.Has(m, known.PulseBodyAttribute);
        var count = exact.GetMembers("Count").OfType<IPropertySymbol>().SingleOrDefault(p =>
            !p.IsStatic && p.Parameters.IsEmpty && p.Type.SpecialType == SpecialType.System_Int32)?.GetMethod;
        var copy = exact.GetMembers("CopyTo").OfType<IMethodSymbol>().SingleOrDefault(m =>
            !m.IsStatic && m.Parameters is [{ Type: IArrayTypeSymbol array }, { Type.SpecialType: SpecialType.System_Int32 }] &&
            array.Rank == 1 && SymbolEqualityComparer.Default.Equals(array.ElementType, element));
        var iface = exact.AllInterfaces.SingleOrDefault(i =>
            i.OriginalDefinition.SpecialType == SpecialType.System_Collections_Generic_IEnumerable_T &&
            SymbolEqualityComparer.Default.Equals(i.TypeArguments[0], element));
        var actual = iface?.GetMembers("GetEnumerator").SingleOrDefault() is { } slot
            ? NominalDispatch.InterfaceSlot(exact, slot) : null;
        var protocol = EnumerationProtocols.Evidence(exact, element, known);
        var witness = protocol ?? actual;
        if (!Checked(count) || !Declarations.IsReadOnly(count!, model.Compilation, known))
            return Refuse("requires a checked nonmutating Count getter.");
        if (!Checked(copy) || !Declarations.IsReadOnly(copy!, model.Compilation, known))
            return Refuse("requires a checked nonmutating CopyTo(array, index).");
        if (!Checked(witness) || Iterators.Element(witness!) is null ||
            !Declarations.IsReadOnly(witness!, model.Compilation, known))
            return Refuse("requires actual checked nonmutating interface enumeration evidence " +
                "(a yield implementation or a validated [EnumerationProtocol] traversal).");
        if (e.Collection) return Refuse("collection-interface capabilities are outside this schema.");
        IrCall Call(IMethodSymbol method, params IrExpr[] args) =>
            new(loc, Naming.Of(method), [owner, .. args]) {
                Kind = CalleeKind.Method, ResultType = known.MapReturnType(method.ReturnType),
                HasReceiver = true, KeepsArguments = true,
                ParamTypes = Declarations.ParamTypes(method, known, true),
                TypeArguments = known.TypeArguments(method), MutatesReceiver = false };
        var items = new IrObserve(loc, ownerType.Name, projection.Name,
            new IrVar(loc, "owner") { Type = ownerType }) { Type = sequence };
        // This ghost-only padding gives the total abstract model its scalar
        // component. A miss installs None, so it cannot expose any scalar getter
        // or assert that the disjoint source has the target's comparer.
        IrExpr scalar = e.Capability!.ScalarType is IrPrim { Kind: PrimKind.Bool }
            ? new IrLiteral(loc, false) { Type = IrPrim.Bool }
            : new IrSpecOp(loc, Sorted.Order + ".default_comparer", []) {
                TypeArgs = ((IrUserSpecType)e.Capability.ScalarType).Args,
                Type = e.Capability.ScalarType };
        var name = Fresh("nominal_snapshot");
        foreach (var tp in WellKnown.DefaultedIn(element)) DefaultedTypeParameters.Add(tp.Name);
        var arrayType = new IrArrayType(e.Element);
        var array = new IrVar(loc, name) { Type = arrayType };
        var yielded = Fresh("nominal_yielded");
        var lengthCall = Call(count!);
        var installation = new IrEnumerationInstallation("Nominal_" + LiftPrefix + "_" + name,
            LiftTypeParameters, e, ownerType, null, null, items, scalar,
            lengthCall.Callee, "", lengthCall.TypeArguments, []) { Matches = false };
        var setup = new List<IrStmt> {
            new IrLocalDecl(loc, name, arrayType,
                new IrNewArray(loc, e.Element, lengthCall) { Type = arrayType }),
            new IrExprStmt(loc, Call(copy!, array, new IrLiteral(loc, 0) { Type = IrPrim.Int }))
        };
        if (protocol is not null && EnumerationProtocols.Resolve(exact, element, known) is { } plan)
            setup.AddRange(EnumerationProtocols.Guard(plan, this, owner, Fresh("factory_guard"), loc));
        setup.Add(new IrLocalDecl(loc, yielded, sequence,
            Call(witness!) with { ResultType = sequence }));
        return new IrStmtExpr(loc, setup.ToImmutableArray(),
            new IrEnumOp(loc, EnumOpKind.Lend, array,
                [owner, new IrVar(loc, yielded) { Type = sequence }]) {
                    Type = e, CastMatch = false, Installation = installation
                }) { Type = e };
    }
}
