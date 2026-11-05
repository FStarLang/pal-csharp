using System.Collections.Immutable;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using Pal.Compiler.Diagnostics;
using Pal.Compiler.Emit;
using Pal.Compiler.Ir;

namespace Pal.Compiler.Frontend;

/// <summary>
/// Lowers bound C# expressions to <see cref="IrExpr"/>.
///
/// <para>
/// The lowering is <em>structure preserving</em> (doc/translation.md §0 rule 2): it
/// neither folds constants, nor reassociates, nor recognises idioms. Every node here
/// maps one C# construct to one IR construct.
/// </para>
/// </summary>
public sealed partial class ExprLowerer(SemanticModel model, WellKnown known, DiagnosticBag diagnostics, bool specPosition)
{
    /// <summary>
    /// True when lowering a specification. In spec position arithmetic is mathematical
    /// (doc/translation.md §6), so no overflow obligations are raised.
    /// </summary>
    public bool SpecPosition { get; } = specPosition;

    /// <summary>
    /// §3.4. The members of the class being lowered, which a body inside that class names
    /// without a receiver: the fields a <c>[Model]</c> abstraction reads, and the
    /// <c>[Model]</c> member a <c>[Spec]</c> observation reads. Each becomes a simple
    /// binder, which is the same convention R3.4 already uses for a struct's
    /// <c>[Refine]</c>, so the emitter binds them and nothing here needs a receiver.
    /// Empty everywhere else, so an unqualified member reference stays unsupported.
    /// </summary>
    public ImmutableHashSet<string> ClassMembers { get; init; } = [];

    /// <summary>
    /// The instance fields of the class whose method is being lowered (§4.5). Inside that
    /// method — and only there — a field name denotes the field itself rather than a
    /// function of the model, because the method holds the representation between the
    /// opening <c>unfold</c> and the closing <c>fold</c>. Outside, the same name is
    /// PALCS0523: a caller holds the model and nothing else.
    /// </summary>
    public ImmutableHashSet<string> ObjectFields { get; init; } = [];

    /// <summary>
    /// R10.2. The type a name was *declared* at, which for a nullable reference is not the
    /// type the expression has: C#'s flow analysis narrows `t` to non-null inside the
    /// `else` of a null test, and rightly so. The encoding cannot follow it there — the
    /// reference is an `option` for its whole life, and what the test bought is the
    /// contents of R10.7's window, not a different type. So a name is typed by its
    /// declaration and nothing else.
    /// </summary>
    /// <summary>
    /// R17.5. Set while lowering the array underneath an implicit borrow, so that the same
    /// syntax — whose converted type is still a span — is not borrowed a second time.
    /// </summary>
    private bool _inImplicitBorrow;

    private IrType? Declared(ExpressionSyntax node)
    {
        if (node is not IdentifierNameSyntax and not MemberAccessExpressionSyntax) return null;
        var symbol = model.GetSymbolInfo(node).Symbol;
        // R21.6. A pattern variable is the value it was bound to, at that value's type:
        // `var` declares it nullable whatever it matched.
        if (symbol is ILocalSymbol pl && _patternBindings.TryGetValue(pl, out var bound)) return bound.Type;
        var declared = symbol switch
        {
            ILocalSymbol l => l.Type,
            IParameterSymbol p => p.Type,
            IFieldSymbol f => f.Type,
            _ => null,
        };
        return declared is null ? null : known.MapType(declared);
    }

    public IrExpr Lower(ExpressionSyntax node)
    {
        var loc = Locations.From(node);
        var info = model.GetTypeInfo(node);
        // R10.2. `null` has no type of its own; what it denotes is fixed by the context,
        // and that is the only thing that says *which* class's `None` this is.
        var type = Declared(node) ?? known.MapType(info.Type)
            ?? (node.IsKind(SyntaxKind.NullLiteralExpression) ? known.MapType(info.ConvertedType) : null);

        // R20.3. A method group converted to a delegate is a value of an opaque type. The
        // method is not called and nothing about it is translated.
        if (info.ConvertedType is { TypeKind: TypeKind.Delegate } &&
            node is IdentifierNameSyntax or MemberAccessExpressionSyntax &&
            model.GetSymbolInfo(node).Symbol is IMethodSymbol group)
            return new IrMethodGroup(loc, $"{group.ContainingType.Name}.{group.Name}")
            { Type = known.MapType(info.ConvertedType) };

        IrExpr result = node switch
        {
            // R17.5. The implicit `T[]` -> `Span<T>` conversion is a *borrow*, so it is
            // matched before anything else: what follows would otherwise lower the array
            // as an array and leave the conversion to disappear silently.
            _ when !_inImplicitBorrow && info.Type is IArrayTypeSymbol { Rank: 1 } &&
                   known.IsAnySpan(info.ConvertedType)
                => LowerImplicitBorrow(node, loc),
            ParenthesizedExpressionSyntax p => Lower(p.Expression),
            // R10.5. `e!` is C#'s null-forgiving operator: it changes what the *C#*
            // compiler's flow analysis believes and nothing else. It is how a model
            // expression says that reading through a nullable reference is deliberate —
            // a null one denotes the empty structure — so it is transparent here, exactly
            // as parentheses are.
            PostfixUnaryExpressionSyntax { RawKind: (int)SyntaxKind.SuppressNullableWarningExpression } sn
                => Lower(sn.Operand),
            // R13.3. An increment in expression position both produces a value and
            // performs a write. Postfix yields the value from *before* the write, prefix
            // from after; that one-word difference is the whole of the distinction.
            PostfixUnaryExpressionSyntax { RawKind: (int)SyntaxKind.PostIncrementExpression } pi
                => Step(pi.Operand, BinOp.Add, before: true, loc),
            PostfixUnaryExpressionSyntax { RawKind: (int)SyntaxKind.PostDecrementExpression } pd
                => Step(pd.Operand, BinOp.Sub, before: true, loc),
            // `default` and `default(T)` are the same expression; both must be matched
            // before the general literal case, which would otherwise see a token with
            // no value and produce a nonsense constant.
            DefaultExpressionSyntax => Default(node, loc),
            LiteralExpressionSyntax l when l.IsKind(SyntaxKind.DefaultLiteralExpression) =>
                Default(node, loc),
            LiteralExpressionSyntax l => LowerLiteral(l, loc),
            ThisExpressionSyntax => new IrVar(loc, Names.This),
            IdentifierNameSyntax id => LowerIdentifier(id, loc),
            MemberAccessExpressionSyntax m => LowerMemberAccess(m, loc),
            ElementAccessExpressionSyntax e => LowerElementAccess(e, loc),
            BinaryExpressionSyntax b when b.IsKind(SyntaxKind.AsExpression) => LowerAs(b, loc),
            BinaryExpressionSyntax b => LowerBinary(b, loc),
            PrefixUnaryExpressionSyntax u => LowerPrefixUnary(u, loc),
            ConditionalExpressionSyntax c =>
                new IrConditional(loc, Lower(c.Condition), Lower(c.WhenTrue), Lower(c.WhenFalse)),
            ConditionalAccessExpressionSyntax ca => LowerConditionalAccess(ca, loc),
            MemberBindingExpressionSyntax mb when _bound is { } bound &&
                                                  known.SpecTypeName(model.GetTypeInfo(BoundSyntax!).Type) is not null =>
                SpecMember(model.GetSymbolInfo(mb).Symbol, [bound], mb, loc),
            // R20.9. `(int)E.Member` is the number C# folds it to: an enum is not a type
            // the translation models, but each of its constants is an integer literal.
            CastExpressionSyntax c when model.GetTypeInfo(c.Expression).Type is { TypeKind: TypeKind.Enum } &&
                                        model.GetConstantValue(c) is { HasValue: true, Value: { } folded } =>
                new IrLiteral(loc, folded),
            CastExpressionSyntax c when known.MapType(model.GetTypeInfo(c.Type).Type) is { } t =>
                new IrConvert(loc, t, Lower(c.Expression)),
            InvocationExpressionSyntax i => LowerInvocation(i, loc),
            ArrayCreationExpressionSyntax a => LowerArrayCreation(a, loc),
            // R17.7. `stackalloc` allocates, and every other allocation in the subset is
            // `new T[n]`, whose translation (R6.9) rests on the CLR's garbage collector.
            // A `stackalloc` span is a stack allocation with a lifetime, which is the one
            // thing `Pulse.Lib.CSharp.Array.alloc` was allowed to assume away.
            StackAllocArrayCreationExpressionSyntax => SpanUnsupported("stackalloc", loc),
            ImplicitStackAllocArrayCreationExpressionSyntax =>
                SpanUnsupported("stackalloc", loc),
            ObjectCreationExpressionSyntax o => LowerObjectCreation(o, loc),
            ImplicitObjectCreationExpressionSyntax o => LowerObjectCreation(o, loc),
            IsPatternExpressionSyntax ip => LowerIsPattern(ip, loc),
            SwitchExpressionSyntax sw => LowerSwitchExpression(sw, loc),
            ThrowExpressionSyntax th => new IrRaise(loc, Lower(th.Expression)) { Type = known.MapType(info.ConvertedType) },
            _ => Unsupported(node, loc),
        };

        // R17.5. A borrow's type is the span it produces, not the array it came from,
        // which is what `info.Type` reports for the syntax the conversion was applied to.
        if (result is IrSpanCreate) type = known.MapType(info.ConvertedType) ?? type;

        if (type is not null) result = result with { Type = type };

        // R21.9. A nullable variable C#'s flow analysis knows is not null, used where a
        // non-nullable value is expected, is its value: `Some?.v`, whose refinement F*
        // proves from the same tests C# drew the conclusion from.
        if (type is IrOptionType declaredOption && info.ConvertedType is { } narrowedTo &&
            known.MapType(narrowedTo) is { } narrowed and not IrOptionType &&
            narrowed.Equals(declaredOption.Inner))
            result = NonNull(result);

        // R20.9. A constant at an `option` type -- an oblivious `string` constant -- is a
        // value that is there: `Some` of it.
        if (type is IrOptionType constOption && result is IrLiteral { Value: not null } constant)
            result = new IrOptionOp(loc, OptionOpKind.Some, constant with { Type = constOption.Inner })
                { Type = constOption };

        // R20.7. An implicit user-defined conversion that is a `[SpecOp]` is an
        // application of its function, wherever C# inserts it.
        if (model.GetConversion(node) is { IsUserDefined: true, IsImplicit: true, MethodSymbol: { } conv } &&
            known.SpecOpName(conv) is { } convOp)
            return new IrSpecOp(loc, convOp, [result])
            {
                Type = known.MapType(info.ConvertedType),
                ParamTypes = Declarations.ParamTypes(conv, known, receiver: false),
            };

        // R20.3. C# converts `T` to `T?` silently; the conversion is `Some`.
        if (type is not null and not IrOptionType && result is not IrNull &&
            known.MapType(info.ConvertedType) is IrOptionType wrapped)
            result = new IrOptionOp(loc, OptionOpKind.Some, result) { Type = wrapped };

        // R9.15. C# inserts a reference conversion silently wherever a derived reference
        // meets a base-typed context — an argument, a `return`, an assignment. The scheme's
        // image of one is a ghost step with a runtime value, so it cannot stay invisible:
        // it is recorded here, at exactly the positions the C# compiler itself inserts it,
        // and the emitter then has a single rule for it wherever it appears.
        if (type is IrClassType && known.MapType(info.ConvertedType) is IrClassType converted &&
            converted.Name != ((IrClassType)type).Name)
        {
            result = new IrConvert(loc, converted, result) { Type = converted };
        }

        // R13.4. The same is true of C#'s implicit numeric promotions, and for the same
        // reason. `b & 0xff` on a `byte` is not a `byte` operation: C# promotes both
        // operands to `int` and applies `int`'s operator. Until R13.1 the promotion could
        // be ignored because no conversion was translated at all, so the operation was
        // silently attributed to the operand's own width — which is a different function.
        //
        // A constant is re-typed rather than converted. `byte b = 5;` converts the
        // literal at compile time, and emitting a cast around it would name a runtime
        // operation the program does not perform.
        if (type is IrPrim { IsMachineInt: true } from &&
            known.MapType(info.ConvertedType) is IrPrim { IsMachineInt: true } to &&
            from.Kind != to.Kind)
        {
            result = result is IrLiteral lit
                ? lit with { Type = to }
                : new IrConvert(loc, to, result) { Type = to };
        }

        return result;
    }

    /// <summary>
    /// R6.9. <c>new T[n]</c>. The CLR zero-fills, so the initial contents are known and
    /// the allocation needs no separate initialisation loop; an explicit initialiser list
    /// would be one, and is refused rather than silently unrolled.
    /// </summary>
    private IrExpr LowerArrayCreation(ArrayCreationExpressionSyntax node, IrLoc loc)
    {
        if (node.Initializer is not null)
        {
            diagnostics.Unsupported(loc, "An array initializer",
                "Allocate with `new T[n]` and assign the elements, so that each write is a " +
                "statement the translation can put a specification between.");
            return new IrLiteral(loc, null);
        }

        if (known.MapType(model.GetTypeInfo(node).Type) is not IrArrayType array ||
            node.Type.RankSpecifiers is not [{ Sizes: [var size] }])
        {
            return Unsupported(node, loc);
        }

        var length = Lower(size);
        // R22.10. `new T[n]` fills with `default(T)`, so at a type parameter it needs the
        // caller's default exactly as R14.2a's `default(T)` does -- unless the length is
        // the literal zero, which fills nothing.
        if (length is not IrLiteral { Value: 0 or 0L } &&
            model.GetTypeInfo(node).Type is IArrayTypeSymbol { ElementType: ITypeParameterSymbol tp })
        {
            DefaultedTypeParameters.Add(tp.Name);
        }
        return new IrNewArray(loc, array.Element, length) { Type = array };
    }

    /// <summary>
    /// R3.5. <c>new S { f = e, … }</c>. Only object-initializer syntax is translated:
    /// a user-written constructor has a body, and running that body at every
    /// construction site is method translation, not expression translation.
    /// </summary>
    /// <summary>
    /// R4.12c. `C(...) : this(args)` is the call `ctor_C_sig(args)`, exactly as `new
    /// C(args)` is: the chained constructor is the one that builds the object, and the
    /// chaining one is a function returning what it returned.
    /// </summary>
    public IrExpr LowerConstructorInitializer(ConstructorInitializerSyntax node)
    {
        var loc = Locations.From(node);
        if (model.GetSymbolInfo(node).Symbol is not IMethodSymbol ctor ||
            ctor.ContainingType is not { } klass || !known.HasModel(klass))
        {
            diagnostics.Unsupported(loc, $"The constructor initializer `{node.ThisOrBaseKeyword}(…)`");
            return new IrLiteral(loc, null);
        }

        return new IrCall(loc, Naming.Of(ctor),
            [.. node.ArgumentList.Arguments.Select(LowerArgument)])
        {
            Kind = CalleeKind.Method,
            ResultType = known.MapType(klass) ?? new IrClassType(klass.Name),
            TypeArguments = known.TypeArguments(ctor),
        };
    }

    private IrExpr LowerObjectCreation(BaseObjectCreationExpressionSyntax node, IrLoc loc)
    {
        // R21.1. A case record is built by its F* constructor.
        if (model.GetTypeInfo(node).Type is INamedTypeSymbol caseType &&
            known.CaseConstructor(caseType) is { } caseCtor)
        {
            if (node.Initializer is not null || known.CaseComponents(caseType).IsDefault)
                return Unsupported(node, loc);
            var caseArgs = (node.ArgumentList?.Arguments ?? default).Select(a => Lower(a.Expression)).ToImmutableArray();
            return new IrSpecOp(loc, caseCtor, caseArgs)
            {
                ParamTypes = model.GetSymbolInfo(node).Symbol is IMethodSymbol cm
                    ? Declarations.ParamTypes(cm, known, receiver: false)
                    : [],
            };
        }

        // R21.7. An exception the BCL declares, built from constants.
        if (model.GetTypeInfo(node).Type is INamedTypeSymbol libExn && known.IsLibraryException(libExn))
        {
            var args = node.ArgumentList?.Arguments ?? default;
            if (node.Initializer is not null ||
                args.Any(a => !model.GetConstantValue(a.Expression).HasValue))
            {
                diagnostics.Error("PALCS0628", loc,
                    $"`{Trim(node)}`. An exception the BCL declares translates when it is built " +
                    "from constants: its message is not modelled (doc/translation.md R21.7).");
                return new IrLiteral(loc, null);
            }
            return LibraryException(loc, libExn.ToDisplayString());
        }

        // R20.7. A `[SpecOp]` constructor of a specification type is an application of its
        // function to the arguments.
        if (model.GetSymbolInfo(node).Symbol is IMethodSymbol { MethodKind: MethodKind.Constructor } specCtor &&
            known.SpecOpName(specCtor) is not null)
        {
            if (node.Initializer is not null)
                return Unsupported(node, loc);
            return SpecMember(specCtor,
                [.. (node.ArgumentList?.Arguments ?? default).Select(a => Lower(a.Expression))], node, loc);
        }

        // R20.10. A BCL value built from constants, or a set from its elements.
        if (model.GetTypeInfo(node).Type is INamedTypeSymbol bclType &&
            Bcl.MapType(bclType, known.MapType) is not null)
        {
            var collection = node.Initializer is { } init &&
                             init.IsKind(SyntaxKind.CollectionInitializerExpression);
            var ctorArgs = node.ArgumentList?.Arguments ?? default;
            var constants = ctorArgs.Select(a => model.GetConstantValue(a.Expression) is { HasValue: true } cv
                ? cv.Value : null).ToImmutableArray();
            var elements = collection
                ? node.Initializer!.Expressions.Select(Lower).ToImmutableArray()
                : [];
            if ((collection ? ctorArgs.Count == 0 : node.Initializer is null) &&
                Bcl.Construct(bclType, constants, elements, collection, loc) is { } built)
                return built;
            diagnostics.Error("PALCS0625", loc,
                $"`{Trim(node)}`. A `{bclType.Name}` translates when it is built from constants, " +
                "or a `HashSet` from a collection initializer (doc/translation.md R20.10).");
            return new IrLiteral(loc, null);
        }

        // R19.1. `new E(args)` of an exception class builds its payload: a pure value, so
        // it may appear anywhere an expression may, and is most often thrown at once.
        if (model.GetTypeInfo(node).Type is INamedTypeSymbol exn && known.IsExceptionClass(exn))
        {
            if (node.Initializer is not null)
            {
                diagnostics.Error("PALCS0613", loc,
                    $"An object initializer on the exception `{exn.Name}`. Its fields are set " +
                    "by its constructor alone (doc/translation.md R19.1).");
                return new IrLiteral(loc, null);
            }
            return new IrNewException(loc, exn.Name,
                [.. (node.ArgumentList?.Arguments ?? default).Select(a => Lower(a.Expression))]);
        }

        // R4.12. `new C(args)` is a call to the constructor's own emitted function. Unlike
        // a struct, a class has a constructor *body* — it allocates — so there is a
        // function to call rather than a record to build.
        if (model.GetTypeInfo(node).Type is INamedTypeSymbol { TypeKind: TypeKind.Class } klass &&
            known.HasModel(klass))
        {
            if (model.GetSymbolInfo(node).Symbol is not IMethodSymbol ctor)
                return Unsupported(node, loc);

            return new IrCall(loc, Naming.Of(ctor),
                [.. (node.ArgumentList?.Arguments ?? default).Select(LowerArgument)])
            {
                Kind = CalleeKind.Method,
                ResultType = known.MapType(klass) ?? new IrClassType(klass.Name),
                // R15.1. A constructor of a generic class is a function of the class's
                // type arguments exactly as any other of its methods is.
                TypeArguments = known.TypeArguments(ctor),
            };
        }

        // R12.4. `new C { f = e, … }` on a `[Plain]` class. Object-initializer syntax and
        // not a constructor call: a constructor has a *body*, and reading a body to learn
        // which parameter lands in which field is exactly the deriving §12 does not do.
        // The initializer says it outright, so the record is built the way R3.5 builds a
        // struct's and then boxed.
        if (model.GetTypeInfo(node).Type is INamedTypeSymbol { TypeKind: TypeKind.Class } plain
            && Declarations.Has(plain.OriginalDefinition, known.PlainAttribute))
        {
            if (node.ArgumentList is { Arguments.Count: > 0 })
            {
                diagnostics.Unsupported(loc, $"A constructor call on the `[Plain]` class `{plain.Name}`",
                    "Use object-initializer syntax: `new " + plain.Name + " { Field = value, … }`. " +
                    "A `[Plain]` class has no emitted constructor, because pal-csharp derives " +
                    "nothing about it (doc/translation.md R12.4).");
                return new IrLiteral(loc, null);
            }

            var inits = new List<IrFieldInit>();
            foreach (var expr in node.Initializer?.Expressions ?? default)
            {
                if (expr is not AssignmentExpressionSyntax { Left: IdentifierNameSyntax pn } pa)
                {
                    diagnostics.Unsupported(Locations.From(expr), $"The initializer `{Trim(expr)}`");
                    continue;
                }
                inits.Add(new IrFieldInit(pn.Identifier.ValueText, Lower(pa.Right)));
            }

            if (Construct(loc, plain.Name, plain, inits) is not IrNew record)
                return new IrLiteral(loc, null);
            return new IrAlloc(loc, plain.Name, record) { Type = known.MapType(plain) ?? new IrClassType(plain.Name) };
        }

        if (model.GetTypeInfo(node).Type is not INamedTypeSymbol { TypeKind: TypeKind.Struct } named)
            return Unsupported(node, loc);

        if (node.ArgumentList is { Arguments.Count: > 0 })
        {
            diagnostics.Unsupported(loc, $"A constructor call on `{named.Name}`",
                "Use object-initializer syntax: `new " + named.Name + " { Field = value, … }`.");
            return new IrLiteral(loc, null);
        }

        var given = new List<IrFieldInit>();
        foreach (var expr in node.Initializer?.Expressions ?? default)
        {
            if (expr is not AssignmentExpressionSyntax { Left: IdentifierNameSyntax name } assign)
            {
                diagnostics.Unsupported(Locations.From(expr), $"The initializer `{Trim(expr)}`");
                continue;
            }
            given.Add(new IrFieldInit(name.Identifier.ValueText, Lower(assign.Right)));
        }

        return Construct(loc, named.Name, named, given);
    }

    /// <summary>
    /// R3.5. Builds the complete field list: C# guarantees a value type is fully
    /// initialized, so a field the source did not mention takes its type's zero.
    /// </summary>
    private IrExpr Construct(
        IrLoc loc, string name, INamedTypeSymbol? symbol,
        IReadOnlyList<IrFieldInit> given)
    {
        if (symbol is null)
        {
            diagnostics.Unsupported(loc, $"A value of type `{name}`");
            return new IrLiteral(loc, null);
        }

        var fields = ImmutableArray.CreateBuilder<IrFieldInit>();
        foreach (var (field, type) in StructFields(symbol))
        {
            var declared = known.MapType(type);
            var supplied = given.FirstOrDefault(g => g.Field == field);
            if (supplied is not null)
            {
                fields.Add(supplied with { FieldType = declared });
                continue;
            }
            if (Zero(loc, type) is not { } zero)
            {
                diagnostics.Unsupported(loc, $"The default value of `{name}.{field}`");
                return new IrLiteral(loc, null);
            }
            fields.Add(new IrFieldInit(field, zero) { FieldType = declared });
        }

        foreach (var g in given)
            if (!fields.Any(f => f.Field == g.Field))
                diagnostics.Unsupported(loc, $"The initializer for `{name}.{g.Field}`");

        return new IrNew(loc, name, fields.ToImmutable());
    }

    /// <summary>The fields of a struct, in declaration order; see R3.4.</summary>
    private static IEnumerable<(string Name, ITypeSymbol Type)> StructFields(INamedTypeSymbol symbol)
    {
        foreach (var member in symbol.GetMembers())
        {
            switch (member)
            {
                case IFieldSymbol { IsStatic: false, IsConst: false, AssociatedSymbol: null } f:
                    yield return (f.Name, f.Type); break;
                case IPropertySymbol { IsStatic: false, IsIndexer: false } p
                    when symbol.GetMembers().OfType<IFieldSymbol>().Any(
                        f => SymbolEqualityComparer.Default.Equals(f.AssociatedSymbol, p)):
                    yield return (p.Name, p.Type); break;
            }
        }
    }

    private IrExpr? Zero(IrLoc loc, ITypeSymbol type)
    {
        var mapped = known.MapType(type);
        return mapped switch
        {
            IrPrim { Kind: PrimKind.Bool } => new IrLiteral(loc, false) { Type = mapped },
            IrPrim p when p.IsMachineInt || p.Kind is PrimKind.SpecInt or PrimKind.SpecNat =>
                new IrLiteral(loc, 0) { Type = mapped },
            IrNamedType n when type is INamedTypeSymbol named =>
                Construct(loc, n.Name, named, []) is IrNew nested ? nested with { Type = mapped } : null,
            _ => null,
        };
    }

    private IrExpr Unsupported(ExpressionSyntax node, IrLoc loc)
    {
        diagnostics.Unsupported(loc, $"The expression `{Trim(node)}`");
        return new IrLiteral(loc, null);
    }

    /// <summary>
    /// R17.5. The implicit <c>T[]</c> to <c>Span&lt;T&gt;</c> conversion, admitted only where
    /// the resulting span gets a name.
    /// </summary>
    /// <remarks>
    /// The conversion borrows, so it produces a receipt, and a receipt has to be redeemed by
    /// a <c>Pal.Restore</c> that names the span. In <c>Span&lt;int&gt; s = a;</c> there is a
    /// name. In <c>Clear(a)</c> there is not: the span exists only for the duration of the
    /// argument list, and the array would be unrecoverable afterwards — not unsoundly, but
    /// with a failure some distance from its cause. Refusing here puts the message where the
    /// mistake is, and the fix is one line: name the borrow, pass the name, restore it.
    /// </remarks>
    private IrExpr LowerImplicitBorrow(ExpressionSyntax node, IrLoc loc)
    {
        if (node.Parent is not EqualsValueClauseSyntax { Parent: VariableDeclaratorSyntax })
        {
            diagnostics.SpanWindow(loc,
                $"the implicit `T[]` to `Span<T>` conversion of `{Trim(node)}` here");
            return new IrLiteral(loc, null);
        }

        _inImplicitBorrow = true;
        try { return new IrSpanCreate(loc, SpanOrigin.Array, Lower(node), null, null); }
        finally { _inImplicitBorrow = false; }
    }

    /// <summary>R17.5. A construct that makes a span which is not the whole of an array.</summary>
    private IrExpr SpanUnsupported(string construct, IrLoc loc)
    {
        diagnostics.SpanWindow(loc, $"`{construct}`");
        return new IrLiteral(loc, null);
    }

    /// <summary>
    /// R17.5. <c>a.AsSpan()</c>, <c>a.AsSpan(i)</c>, <c>a.AsSpan(i, n)</c>,
    /// <c>s.Slice(i)</c> and <c>s.Slice(i, n)</c> — the five ways to name a borrow.
    /// Returns null when the call is not one of them, so that the caller can fall through
    /// to R17.7's refusal with a message naming the method that was actually written.
    /// </summary>
    /// <remarks>
    /// The one-argument forms borrow to the end, which is a length the *source* knows and
    /// the call site does not write. Rather than invent a second library operation for it,
    /// the missing length is filled in as <c>source.Length - start</c>: an expression the
    /// user could have written, built from the same receiver they did write. That keeps one
    /// creation rule per origin rather than two, and makes `s.Slice(i)` and
    /// `s.Slice(i, s.Length - i)` translate identically, which they should.
    /// </remarks>
    private IrExpr? LowerBorrow(
        IMethodSymbol method,
        MemberAccessExpressionSyntax access,
        SeparatedSyntaxList<ArgumentSyntax> args,
        IrLoc loc)
    {
        var sourceType = model.GetTypeInfo(access.Expression).Type;
        var fromSpan = known.IsAnySpan(sourceType);
        var fromArray = sourceType is IArrayTypeSymbol { Rank: 1 };

        var expected = fromSpan ? "Slice" : "AsSpan";
        if (method.Name != expected || (!fromSpan && !fromArray) || args.Count > 2) return null;

        var source = Lower(access.Expression);
        var origin = fromSpan ? SpanOrigin.SpanRange : SpanOrigin.ArrayRange;

        if (args.Count == 0)
        {
            // `a.AsSpan()` borrows the whole array, which has its own receipt and its own
            // `Pal.Restore` — the one that gives the array back unspliced.
            if (fromArray) return new IrSpanCreate(loc, SpanOrigin.Array, source, null, null);
            // `s.Slice()` does not exist; a zero-argument `Slice` is not ours.
            return null;
        }

        var start = Lower(args[0].Expression);
        var length = args.Count == 2
            ? Lower(args[1].Expression)
            : new IrBinary(loc, BinOp.Sub, new IrLength(loc, source), start);

        return new IrSpanCreate(loc, origin, source, start, length);
    }

    /// <summary>
    /// R17.5. <c>s[i..j]</c>. C#'s range syntax admits an omitted endpoint and an
    /// end-relative <c>^k</c>; the first is ordinary sugar and is filled in the way
    /// <see cref="LowerBorrow"/> fills in an omitted length, and the second is refused,
    /// because <c>^k</c> denotes <c>Length - k</c> only after an <c>Index</c> value has been
    /// constructed, and that value is a struct the subset does not translate.
    /// </summary>
    private IrExpr LowerRangeWindow(ExpressionSyntax receiver, RangeExpressionSyntax range, IrLoc loc)
    {
        if (range.LeftOperand is PrefixUnaryExpressionSyntax { RawKind: (int)SyntaxKind.IndexExpression } ||
            range.RightOperand is PrefixUnaryExpressionSyntax { RawKind: (int)SyntaxKind.IndexExpression })
        {
            return SpanUnsupported("an end-relative index `^k` in a range", loc);
        }

        var source = Lower(receiver);
        var start = range.LeftOperand is { } lo ? Lower(lo) : new IrLiteral(loc, 0);
        var end = range.RightOperand is { } hi ? Lower(hi) : new IrLength(loc, source);
        return new IrSpanCreate(loc, SpanOrigin.SpanRange, source, start,
                                new IrBinary(loc, BinOp.Sub, end, start));
    }

    /// <summary>
    /// R11.2/R11.3. Lowers a member of a user-declared specification type to the F* term
    /// it declares. There are exactly two ways for a member to have a meaning — it carries
    /// <c>[SpecOp]</c>, or it carries <c>[SpecCtor]</c> — and a third case would be the
    /// translator guessing an F* name from a C# one, which §0 rule 3 forbids. So the
    /// remaining case is a refusal, and that is what makes the mechanism total.
    /// </summary>
    /// <summary>
    /// R20.7. Whether each type parameter of a generic <c>[SpecOp]</c> occurs in one of its
    /// parameter types, so that F* infers it from the arguments (an implicit <c>#a</c>, as
    /// in <c>Tree.khas</c>). When one does not (<c>GetAttributeValue&lt;T&gt;(string)</c>),
    /// nothing determines it but the type argument, and the operation takes the type
    /// arguments explicitly, ahead of its value arguments.
    /// </summary>
    private static bool InferableTypeParameters(IMethodSymbol method) =>
        method.OriginalDefinition.TypeParameters.All(tp =>
            method.OriginalDefinition.Parameters.Any(p => Mentions(p.Type, tp)));

    private static bool Mentions(ITypeSymbol type, ITypeParameterSymbol tp) => type switch
    {
        ITypeParameterSymbol t => SymbolEqualityComparer.Default.Equals(t, tp),
        IArrayTypeSymbol a => Mentions(a.ElementType, tp),
        INamedTypeSymbol n => n.TypeArguments.Any(a => Mentions(a, tp)),
        _ => false,
    };

    private IrExpr SpecMember(ISymbol? symbol, ImmutableArray<IrExpr> args,
                              ExpressionSyntax node, IrLoc loc)
    {
        if (known.SpecOpName(symbol) is { } op)
            return new IrSpecOp(loc, op, args)
            {
                ParamTypes = SpecParamTypes(symbol, args),
                TypeArgs = symbol is IMethodSymbol { IsGenericMethod: true } generic &&
                           !InferableTypeParameters(generic)
                    ? known.TypeArguments(generic) : [],
            };

        // R21.2. A component of a case record.
        if (symbol is IPropertySymbol prop && args.Length == 1 && Projection(prop, args[0], loc) is { } projected)
            return projected;

        if (symbol is not null &&
            Declarations.Find(symbol, known.SpecCtorAttribute) is { } data &&
            Declarations.StringArgument(data) is { } ctor)
            return new IrSpecOp(loc, ctor, args)
            {
                SiblingEmpty = EmptyCtor(symbol, data),
                ParamTypes = SpecParamTypes(symbol, args),
            };

        diagnostics.Error("PALCS0573", loc,
            $"`{Trim(node)}` names a member of a specification type that does not say what " +
            "it means in F*. Mark it `[SpecOp(\"...\")]`, or `[SpecCtor(\"...\")]` if it is a " +
            "constructor (doc/translation.md R11.2). The translator will not guess an F* name " +
            "from a C# one.");
        return new IrLiteral(loc, null);
    }

    /// <summary>
    /// The declared parameter types of a specification operation, when it is a method
    /// whose arity matches the arguments lowered for it. An instance member puts the
    /// receiver first, and the receiver has no declared parameter, so the two only line up
    /// for a static call; anything else contributes no types and no coercion.
    /// </summary>
    private ImmutableArray<IrType?> SpecParamTypes(ISymbol? symbol, ImmutableArray<IrExpr> args) =>
        symbol is IMethodSymbol m && m.Parameters.Length == args.Length
            ? Declarations.ParamTypes(m, known, receiver: false)
            : [];

    /// <summary>
    /// R11.3. The empty constructor of this constructor's type — the sibling declared
    /// alongside it with <c>Empty = true</c>. A use of one constructor is where the other
    /// becomes findable, which is why §10 can invert a `[Model]` without a registry of
    /// specification types.
    /// </summary>
    private string? EmptyCtor(ISymbol ctor, AttributeData self)
    {
        if (Declarations.NamedFlag(self, "Empty")) return Declarations.StringArgument(self);
        if (ctor.ContainingType is not { } owner) return null;
        foreach (var sibling in owner.GetMembers())
        {
            if (Declarations.Find(sibling, known.SpecCtorAttribute) is { } data &&
                Declarations.NamedFlag(data, "Empty"))
                return Declarations.StringArgument(data);
        }
        return null;
    }

    /// <summary>
    /// R20.10. A <c>static readonly</c> field whose initializer is a pure value -- a BCL
    /// model built from constants -- denotes that value. The field is assigned once, before
    /// any method runs, and never again, so naming it and writing its initializer out are
    /// the same expression. An initializer that is not pure is refused here. It is program
    /// text, so it is lowered as code -- at machine integers -- even when a contract names
    /// the field (R20.12): `{ 0, 1 }` is a set of `I32.t` wherever it is read.
    /// </summary>
    private IrExpr? StaticInitializer(IFieldSymbol field, IrLoc loc)
    {
        if (field.DeclaringSyntaxReferences is not [var reference] ||
            reference.GetSyntax() is not VariableDeclaratorSyntax { Initializer.Value: { } init } ||
            !model.Compilation.ContainsSyntaxTree(init.SyntaxTree))
            return null;

        var lowered = new ExprLowerer(
            model.Compilation.GetSemanticModel(init.SyntaxTree), known, diagnostics, specPosition: false)
            .Lower(init);
        if (IsPureValue(lowered)) return lowered with { Loc = loc };
        // R22.8. A shared empty array is read as a fresh one. It has no cells, so no write
        // through either can be observed through the other, and reference identity, the
        // one thing that tells them apart, has no translation (R18.1).
        if (!SpecPosition && lowered is IrNewArray { Length: IrLiteral { Value: 0 } })
            return lowered with { Loc = loc };

        diagnostics.Error("PALCS0626", loc,
            $"`{field.Name}` is a `static readonly` field whose initializer is not a value the " +
            "translation models. A shared field denotes its initializer only when that is a BCL " +
            "model built from constants (doc/translation.md R20.10).");
        return new IrLiteral(loc, null);
    }

    private static bool IsPureValue(IrExpr e) => e switch
    {
        IrLiteral { Value: not null } or IrNull => true,
        IrOptionOp o => IsPureValue(o.Operand),
        IrSpecOp s => s.Args.All(IsPureValue),
        _ => false,
    };

    private static string Trim(SyntaxNode node)
    {
        var text = node.ToString();
        return text.Length <= 60 ? text : text[..57] + "...";
    }

    private static IrExpr LowerLiteral(LiteralExpressionSyntax node, IrLoc loc) =>
        // R10.2. `null` is `None`, and it is a node of its own: an `IrLiteral` at a null
        // value is what a failed lowering produces, and the two must never be confused.
        node.IsKind(SyntaxKind.NullLiteralExpression)
            ? new IrNull(loc)
            : new IrLiteral(loc, node.Token.Value);

    /// <summary>R3.5. <c>default</c> at any translatable type.</summary>
    /// <summary>
    /// R20.12. In a contract, the shim parameters that stand for the receiver's context
    /// fields, by field name.
    /// </summary>
    public ImmutableDictionary<string, ISymbol> ContextNames { get; init; } =
        ImmutableDictionary<string, ISymbol>.Empty;

    /// <summary>R20.12. A read of a receiver-free method's context field.</summary>
    private IrExpr ContextRead(ISymbol field) =>
        new IrVar(Locations.From(field.Locations.FirstOrDefault() ?? Location.None),
                  Declarations.ContextName(field)) { Type = known.MapType(Declarations.ContextType(field)) };

    /// <summary>R14.2a. The method type parameters a <c>default</c> was taken at.</summary>
    public HashSet<string> DefaultedTypeParameters { get; } = [];

    private IrExpr Default(ExpressionSyntax node, IrLoc loc)
    {
        if (model.GetTypeInfo(node).Type is not { } type) return Unsupported(node, loc);
        if (Zero(loc, type) is { } zero) return zero;

        // R14.2a. `default(T)` at an unconstrained `T` is whatever `T`'s default is, which
        // only the caller knows: it is the `has_default` dictionary the caller passes.
        if (type is ITypeParameterSymbol tp &&
            known.MapType(tp) is { } tpType)
        {
            DefaultedTypeParameters.Add(tp.Name);
            return new IrSpecOp(loc, "Pulse.Lib.CSharp.Inhabited.default_of", [])
                { TypeArgs = [tpType], Type = tpType };
        }
        diagnostics.Unsupported(loc, $"`default` at type `{type}`");
        return new IrLiteral(loc, null);
    }

    private IrExpr LowerIdentifier(IdentifierNameSyntax node, IrLoc loc)
    {
        var symbol = model.GetSymbolInfo(node).Symbol;

        // A postcondition's `Result` is a parameter of the generated shim, not a name in
        // the user's program; it denotes the value the method returns.
        if (symbol is IParameterSymbol { Name: SpecBinder.ResultParameter } p &&
            p.ContainingSymbol.Name.StartsWith(SpecBinder.ShimMethodPrefix, StringComparison.Ordinal))
            return new IrResult(loc);

        // R21.3. A pattern variable is the expression it was bound to.
        if (symbol is ILocalSymbol pl && _patternBindings.TryGetValue(pl, out var bound)) return bound;
        if (symbol is IFieldSymbol ef && known.CaseConstructor(ef) is { } enumCtor)
            return new IrSpecOp(loc, enumCtor, []);

        return symbol switch
        {
            IParameterSymbol cp when ContextNames.TryGetValue(cp.Name, out var cf) &&
                cp.ContainingSymbol.Name.StartsWith(SpecBinder.ShimMethodPrefix, StringComparison.Ordinal) =>
                cf is IFieldSymbol { IsStatic: true } sf
                    ? StaticInitializer(sf, loc) ?? Unsupported(node, loc)
                    : new IrVar(loc, Declarations.ContextName(cf)),
            // R20.12a. A captured primary-constructor parameter, read by a method.
            IParameterSymbol { ContainingSymbol: IMethodSymbol { MethodKind: MethodKind.Constructor, ContainingType: { } powner } } pp
                when known.AnnotatedOnly && !known.HasModel(powner) &&
                     model.GetEnclosingSymbol(node.SpanStart) is IMethodSymbol { MethodKind: not MethodKind.Constructor } &&
                     Declarations.ContextFields(powner, model.Compilation, known)
                         .Contains(pp, SymbolEqualityComparer.Default) => ContextRead(pp),
            IParameterSymbol or ILocalSymbol or IRangeVariableSymbol => new IrVar(loc, node.Identifier.ValueText),
            IFieldSymbol f when f.HasConstantValue => new IrLiteral(loc, f.ConstantValue),
            IFieldSymbol { IsStatic: true, IsReadOnly: true } shared
                when StaticInitializer(shared, loc) is { } inlined => inlined,
            IFieldSymbol or IPropertySymbol when ClassMembers.Contains(node.Identifier.ValueText) =>
                new IrVar(loc, node.Identifier.ValueText),
            IFieldSymbol { IsStatic: false, IsReadOnly: true, ContainingType: { } owner } f
                when known.AnnotatedOnly && !known.HasModel(owner) &&
                     Declarations.ContextFields(owner, model.Compilation, known)
                         .Contains(f, SymbolEqualityComparer.Default) => ContextRead(f),
            IFieldSymbol { IsStatic: false } when ObjectFields.Contains(node.Identifier.ValueText) =>
                new IrField(loc, new IrVar(loc, Names.This), node.Identifier.ValueText),
            // R9.20a. `Span` and `this.Span` are the same reference, so they lower to the
            // same node -- writing the receiver out is a style choice, and §7.2 requires
            // that style choices do not reach the emitter.
            IPropertySymbol prop when ComputedRead(prop, loc, new IrVar(loc, Names.This)) is { } call
                => call,
            _ => Unsupported(node, loc),
        };
    }

    /// <summary>
    /// R9.20a. A read of a computed property, in an executable position, is the call its
    /// getter is: <c>g.Span</c> and <c>g.Span()</c> produce identical Pulse. In a
    /// specification this returns <c>null</c>, because a contract reads the model and a
    /// computed property is code over the representation, exactly as a method is.
    /// </summary>
    private IrCall? ComputedRead(IPropertySymbol prop, IrLoc loc, IrExpr receiver)
    {
        if (SpecPosition) return null;
        if (prop.GetMethod is not { } getter) return null;
        if (Declarations.Has(prop, known.SpecAttribute)) return null;
        if (Declarations.Has(prop, known.ModelAttribute)) return null;
        if (Declarations.KindOf(getter, known) is null) return null;

        return new IrCall(loc, Naming.Of(getter), [receiver])
        {
            Kind = CalleeKind.Method,
            ResultType = known.MapType(prop.Type),
            HasReceiver = true,
            ParamTypes = Declarations.ParamTypes(getter, known, true),
            TypeArguments = known.TypeArguments(getter),
            MutatesReceiver = false,
        };
    }

    /// <summary>
    /// R22.21. <c>P = v</c>, for a property with a translated setter, is the call the
    /// setter is, as R9.20a's read is the getter's.
    /// </summary>
    public IrCall? ComputedWrite(AssignmentExpressionSyntax node, IrLoc loc)
    {
        if (SpecPosition || !node.IsKind(SyntaxKind.SimpleAssignmentExpression)) return null;
        if (model.GetSymbolInfo(node.Left).Symbol is not IPropertySymbol { IsIndexer: false } prop) return null;
        if (prop.SetMethod is not { } setter) return null;
        if (Declarations.Has(prop, known.SpecAttribute) || Declarations.Has(prop, known.ModelAttribute)) return null;
        if (Declarations.KindOf(setter, known) is null) return null;
        IrExpr receiver = node.Left switch
        {
            IdentifierNameSyntax => new IrVar(loc, Names.This) { Type = Enclosing(node) },
            MemberAccessExpressionSyntax { Expression: ThisExpressionSyntax } =>
                new IrVar(loc, Names.This) { Type = Enclosing(node) },
            MemberAccessExpressionSyntax m => Lower(m.Expression),
            _ => new IrLiteral(loc, null),
        };
        if (receiver is IrLiteral) return null;
        return new IrCall(loc, Naming.Of(setter), [receiver, ToDeclared(Lower(node.Right), known.MapType(setter.Parameters[0].Type))])
        {
            Kind = CalleeKind.Method,
            ResultType = known.MapType(setter.ReturnType),
            HasReceiver = true,
            ParamTypes = Declarations.ParamTypes(setter, known, true),
            TypeArguments = known.TypeArguments(setter),
            MutatesReceiver = !Declarations.IsReadOnly(setter, model.Compilation),
        };
    }

    private IrExpr LowerMemberAccess(MemberAccessExpressionSyntax node, IrLoc loc)
    {
        var symbol = model.GetSymbolInfo(node).Symbol;
        var receiverType = model.GetTypeInfo(node.Expression).Type;

        if (Bcl.Member(symbol, loc) is { } bclMember) return bclMember;
        // R21.8. A constant of a `[SpecType]` enum is its constructor.
        if (symbol is IFieldSymbol ef && known.CaseConstructor(ef) is { } enumCtor)
            return new IrSpecOp(loc, enumCtor, []);
        // R21.5. A static member bound to an F* term is that term.
        if (symbol is IPropertySymbol { IsStatic: true } or IFieldSymbol { IsStatic: true } &&
            known.SpecOpName(symbol) is { } staticOp)
            return new IrSpecOp(loc, staticOp, []);
        if (symbol is IFieldSymbol { IsStatic: true, IsReadOnly: true } shared &&
            StaticInitializer(shared, loc) is { } inlined)
            return inlined;

        // R14.1b. `g.Value` on a `Ghost<T>` is the ghost value, and is transparent — exactly
        // as `Ghost<T>` is transparent in a type (R14.1) and as a spec string, which is
        // bound against parameters already unwrapped, never has to write it at all. A
        // statement-position specification is an ordinary C# expression, so there `Ghost<T>`
        // is a real type and C# demands the projection; nothing about the *meaning* changes
        // when it is written, so nothing here does either.
        if (known.IsGhost(receiverType) && node.Name.Identifier.ValueText == "Value")
            return Lower(node.Expression);

        // R20.3. `x.HasValue` and `x.Value` on a `T?`. Reading `Value` obliges the
        // prover to show `HasValue`, which is what C#'s exception on a null makes it.
        if (receiverType is INamedTypeSymbol { OriginalDefinition.SpecialType: SpecialType.System_Nullable_T })
        {
            var op = node.Name.Identifier.ValueText switch
            {
                "HasValue" => OptionOpKind.HasValue,
                "Value" => OptionOpKind.Value,
                _ => (OptionOpKind?)null,
            };
            if (op is null) return Unsupported(node, loc);
            return new IrOptionOp(loc, op.Value, Lower(node.Expression));
        }

        // R20.4. A list's `Count` is an array's `Length`.
        if (WellKnown.IsListLike(receiverType) && node.Name.Identifier.ValueText == "Count")
            return new IrLength(loc, Lower(node.Expression));

        // R10.5. The ghost inductive types' observations. They are recognised by symbol,
        // before any class rule, because `SpecList<T>` is a struct and would otherwise
        // fall through to the struct-field rule.
        if (known.IsSpecList(receiverType))
        {
            var op = node.Name.Identifier.ValueText switch
            {
                "Length" => ListOpKind.Length,
                "IsEmpty" => ListOpKind.IsEmpty,
                "Head" => ListOpKind.Head,
                "Tail" => ListOpKind.Tail,
                _ => (ListOpKind?)null,
            };
            if (op is null) return Unsupported(node, loc);
            return new IrListOp(loc, op.Value, [Lower(node.Expression)]);
        }

        // R11.2. A member of a user-declared specification type. The receiver becomes the
        // first argument, which is the same rule for a property and for an instance
        // method, and the same rule a discriminator needs (F44).
        if (known.SpecTypeName(receiverType) is not null)
            return SpecMember(symbol, [NonNull(Lower(node.Expression))], node, loc);

        // `a.Length` on a real array is a pure function of the array (doc §3, R3.3).
        // R17.3. A span's `Length` is `Slice.len`, which is likewise pure and non-ghost, so
        // a counted loop over a span has an ordinary pure guard just as one over an array
        // does. `IrLength` covers both; the emitter picks the library by the operand's type.
        if (node.Name.Identifier.ValueText == "Length" &&
            (receiverType is IArrayTypeSymbol || known.IsAnySpan(receiverType)))
            return new IrLength(loc, Lower(node.Expression));

        // R17.7. Every *other* member of a span is refused here rather than left to fall
        // through to the struct-field rule below, which would project a field out of a
        // slot kind that has no fields. `Length`, the indexer, `Slice` and `AsSpan` are the
        // whole of §17's surface.
        if (known.IsAnySpan(receiverType))
            return SpanUnsupported($"Span<T>.{node.Name.Identifier.ValueText}", loc);

        // `s.Length` on a ghost sequence is `Seq.length`.
        if (node.Name.Identifier.ValueText == "Length" && known.IsSeq(receiverType))
            return new IrSeqOp(loc, SeqOpKind.Length, [Lower(node.Expression)]);

        if (symbol is IFieldSymbol { HasConstantValue: true } konst)
            return new IrLiteral(loc, konst.ConstantValue);

        // R22.18. `Array.MaxLength` is a property only so that the runtime may change it;
        // the value is documented, 0x7FFFFFC7, and it is that literal.
        if (symbol is IPropertySymbol { Name: "MaxLength", IsStatic: true } ml &&
            ml.ContainingType.SpecialType == SpecialType.System_Array)
            return new IrLiteral(loc, 0x7FFFFFC7);

        // R19.1. A field of an exception is a projection out of its payload.
        if (symbol is IFieldSymbol or IPropertySymbol && receiverType is INamedTypeSymbol rt &&
            (known.IsExceptionClass(rt) || known.IsSystemException(rt)))
        {
            if (!known.IsExceptionClass(symbol.ContainingType))
            {
                diagnostics.Error("PALCS0611", loc,
                    $"`{node}` reads a member of `System.Exception`. Only the fields an exception " +
                    "class of the program declares are modelled (doc/translation.md R19.1).");
                return new IrLiteral(loc, null);
            }
            return new IrField(loc, Lower(node.Expression), node.Name.Identifier.ValueText);
        }

        if (symbol is IFieldSymbol or IPropertySymbol && receiverType?.TypeKind == TypeKind.Struct)
            return new IrField(loc, Lower(node.Expression), node.Name.Identifier.ValueText);

        // `this.f` and a bare `f` are the same reference, so they must lower to the same
        // node: writing the receiver out is a style choice, and §7.2 requires that style
        // choices do not reach the emitter. Which node that is depends on where we are —
        // a class-level clause binds fields directly, a method body reaches them through
        // the box — and both cases are decided exactly as they are for the bare name.
        if (node.Expression is ThisExpressionSyntax && symbol is IFieldSymbol or IPropertySymbol)
        {
            var member = node.Name.Identifier.ValueText;
            if (ClassMembers.Contains(member)) return new IrVar(loc, member);
            if (symbol is IFieldSymbol { IsStatic: false } && ObjectFields.Contains(member))
                return new IrField(loc, new IrVar(loc, Names.This), member);
        }

        // R12.3. A field of a `[Plain]` class. There is no model to read instead and no
        // `[Spec]` member to prefer, because §12 derived nothing: the representation is all
        // there is, so a field read is the only thing this can mean. Whether the read is
        // *owned* is settled by the user's predicate when the emitter checks the window,
        // not here.
        if (receiverType is INamedTypeSymbol { TypeKind: TypeKind.Class } plain
            && Declarations.Has(plain.OriginalDefinition, known.PlainAttribute)
            && symbol is IFieldSymbol { IsStatic: false })
            return new IrField(loc, Lower(node.Expression), node.Name.Identifier.ValueText);

        // R3.9c: reading a member off an object. Only a [Spec] member is readable, because
        // a caller holds the model and nothing else; a field read here would be a fact
        // about the representation, which no caller can see.
        if (receiverType is INamedTypeSymbol { TypeKind: TypeKind.Class } owner && known.HasModel(owner))
        {
            // R9.19. The *declaring* class, which at depth three need not be the receiver's
            // static type: `q.TheArea` reads a `Shape` member off a `Quadrilateral`. The
            // observation belongs to the class that declares it, and getting from the
            // receiver's model to that class's is R9.6's forgetting, which the spec emitter
            // composes. Recording the static type here instead would name a spec function
            // that does not exist.
            // R10.5. Reading the `[Model]` member off a reference *is* the model — that
            // is what the model member means. It is how a recursive class's abstraction
            // names its sub-model (`next.Items`), and it is sound anywhere: the model is
            // exactly what a caller holds.
            if (symbol is not null && Declarations.Has(symbol, known.ModelAttribute))
                return Lower(node.Expression);

            if (symbol is not null && Declarations.Has(symbol, known.SpecAttribute))
                return new IrObserve(
                    loc, symbol.ContainingType?.Name ?? owner.Name,
                    node.Name.Identifier.ValueText, Lower(node.Expression));

            // R10.8. A recursive class's fields *are* reachable from outside it, because
            // the window R10.7 opens is one the client's own null test opened: `elim_cons`
            // hands back the head cell, so between the test and the end of the branch the
            // representation is as available to a client as it is to a method of the class.
            // This is the C# a linked list is actually written in — the traversal is not a
            // method of the node, and the node's fields are `internal` for exactly this
            // reason. Outside a window the emitter refuses (PALCS0567); it does not have to
            // be refused here, because the reference is still an `option` there and there
            // is nothing to project.
            if (symbol is IFieldSymbol { IsStatic: false } && WellKnown.IsRecursive(owner))
                return new IrField(loc, Lower(node.Expression), node.Name.Identifier.ValueText);

            // R9.20a. In an executable position a computed property read *is* a call:
            // `r.Doubled` and `r.Doubled()` produce the same Pulse, which is what §7.2
            // requires of a style choice. In a specification it is not, and falls through
            // to PALCS0523 below: a contract reads the model, and a computed property is
            // code over the representation, exactly as an ordinary method is.
            if (symbol is IPropertySymbol prop
                && ComputedRead(prop, loc, Lower(node.Expression)) is { } call)
                return call;

            diagnostics.Error("PALCS0523", loc,
                $"`{node.Name.Identifier.ValueText}` is not a `[Spec]` member of `{owner.Name}`, so a " +
                "contract cannot read it. A caller holds the object's model, not its fields — widen the " +
                "model and expose the quantity as a `[Spec]` member.");
            return new IrLiteral(loc, null);
        }

        return Unsupported(node, loc);
    }

    private IrExpr LowerElementAccess(ElementAccessExpressionSyntax node, IrLoc loc)
    {
        if (node.ArgumentList.Arguments.Count != 1)
        {
            diagnostics.Unsupported(loc, "Multi-dimensional indexing");
            return new IrLiteral(loc, null);
        }

        var receiverType = model.GetTypeInfo(node.Expression).Type;

        // R17.5. `s[i..j]` is a window, and it reaches here as an element access whose one
        // argument is a range. It borrows exactly as `s.Slice(i, j - i)` does.
        //
        // The same syntax on an *array* is a different operation: `a[i..j]` calls
        // `RuntimeHelpers.GetSubArray`, which allocates and *copies*. It borrows nothing,
        // shares nothing, and must not be lowered to a window; R17.7 refuses it, and the
        // fall-through below reaches `Unsupported` for it.
        if (node.ArgumentList.Arguments[0].Expression is RangeExpressionSyntax range)
        {
            if (!known.IsAnySpan(receiverType)) return SpanUnsupported("a[i..j]", loc);
            return LowerRangeWindow(node.Expression, range, loc);
        }

        // R20.7. A `[SpecOp]` indexer read is an application of its function, receiver
        // first, as a `[SpecOp]` method's is.
        if (model.GetSymbolInfo(node).Symbol is IPropertySymbol { IsIndexer: true } indexer &&
            known.SpecOpName(indexer) is not null)
            return SpecMember(indexer,
                [NonNull(Lower(node.Expression)), Lower(node.ArgumentList.Arguments[0].Expression)],
                node, loc);

        var receiver = Lower(node.Expression);
        var index = Lower(node.ArgumentList.Arguments[0].Expression);

        if (known.IsSpecList(receiverType))
            return new IrListOp(loc, ListOpKind.Index, [receiver, index]);

        return known.IsSeq(receiverType)
            ? new IrSeqOp(loc, SeqOpKind.Index, [receiver, index])
            : new IrElement(loc, receiver, index);
    }

    private IrExpr LowerBinary(BinaryExpressionSyntax node, IrLoc loc)
    {
        var op = node.Kind() switch
        {
            SyntaxKind.AddExpression => BinOp.Add,
            SyntaxKind.SubtractExpression => BinOp.Sub,
            SyntaxKind.MultiplyExpression => BinOp.Mul,
            SyntaxKind.DivideExpression => BinOp.Div,
            SyntaxKind.ModuloExpression => BinOp.Rem,
            SyntaxKind.LogicalAndExpression => BinOp.And,
            SyntaxKind.LogicalOrExpression => BinOp.Or,
            SyntaxKind.BitwiseAndExpression => BinOp.BitAnd,
            SyntaxKind.BitwiseOrExpression => BinOp.BitOr,
            SyntaxKind.ExclusiveOrExpression => BinOp.BitXor,
            SyntaxKind.LeftShiftExpression => BinOp.Shl,
            SyntaxKind.RightShiftExpression => BinOp.Shr,
            SyntaxKind.EqualsExpression => BinOp.Eq,
            SyntaxKind.NotEqualsExpression => BinOp.Ne,
            SyntaxKind.LessThanExpression => BinOp.Lt,
            SyntaxKind.LessThanOrEqualExpression => BinOp.Le,
            SyntaxKind.GreaterThanExpression => BinOp.Gt,
            SyntaxKind.GreaterThanOrEqualExpression => BinOp.Ge,
            _ => (BinOp?)null,
        };

        if (node.IsKind(SyntaxKind.CoalesceExpression)) return LowerCoalesce(node, loc);
        // R21.5. A user-defined operator bound to an F* function is an application of it.
        if (model.GetSymbolInfo(node).Symbol is IMethodSymbol { MethodKind: MethodKind.UserDefinedOperator } uop &&
            known.SpecOpName(uop) is { } opName)
            return new IrSpecOp(loc, opName, [NonNull(Lower(node.Left)), NonNull(Lower(node.Right))])
            {
                ParamTypes = Declarations.ParamTypes(uop, known, receiver: false),
            };
        if (op is null) return Unsupported(node, loc);
        var left = Lower(node.Left);
        var right = Lower(node.Right);
        // R20.11. `x == null` compares with the `None` of `x`'s own option type: C# types
        // the `null` of a reference comparison as `object`, which has no translation.
        if (op is BinOp.Eq or BinOp.Ne)
        {
            if (right is IrNull && right.Type is not IrOptionType && left.Type is IrOptionType lt)
                right = right with { Type = lt };
            else if (left is IrNull && left.Type is not IrOptionType && right.Type is IrOptionType rt)
                left = left with { Type = rt };
        }
        return new IrBinary(loc, op.Value, left, right)
        {
            Wraps = op is BinOp.Add or BinOp.Sub or BinOp.Mul && InWrappingMethod(node),
        };
    }

    /// <summary>R22.14. The node sits in a method marked <c>[Wrapping]</c>.</summary>
    private bool InWrappingMethod(SyntaxNode node) =>
        model.GetEnclosingSymbol(node.SpanStart) is IMethodSymbol m &&
        Declarations.Has(m, known.WrappingAttribute);

    /// <summary>
    /// R20.11. <c>a ?? b</c> evaluates <c>a</c> once, and <c>b</c> only when <c>a</c> is
    /// null: <c>let t = a in if Some? t then Some?.v t else b</c>, or <c>t</c> in the then
    /// branch when <c>b</c> is itself nullable.
    /// </summary>
    private IrExpr LowerCoalesce(BinaryExpressionSyntax node, IrLoc loc)
    {
        var tested = Lower(node.Left);
        var fallback = Lower(node.Right);
        if (tested.Type is not IrOptionType inner) return Unsupported(node, loc);

        var prelude = ImmutableArray.CreateBuilder<IrStmt>();
        var subject = tested;
        if (HasEffect(tested))
        {
            var name = Fresh("coalesce");
            prelude.Add(new IrLocalDecl(loc, name, inner, tested) { Immutable = true });
            subject = new IrVar(loc, name) { Type = inner };
        }

        var resultType = fallback.Type is IrOptionType ? inner : fallback.Type ?? inner.Inner;
        IrExpr present = fallback.Type is IrOptionType
            ? subject
            : new IrOptionOp(loc, OptionOpKind.Value, subject) { Type = inner.Inner };
        var conditional = new IrConditional(loc,
            new IrOptionOp(loc, OptionOpKind.HasValue, subject) { Type = new IrPrim(PrimKind.Bool) },
            present, fallback) { Type = resultType };
        return prelude.Count == 0
            ? conditional
            : new IrStmtExpr(loc, prelude.ToImmutable(), conditional) { Type = resultType };
    }

    private IrExpr LowerPrefixUnary(PrefixUnaryExpressionSyntax node, IrLoc loc)
    {
        var op = node.Kind() switch
        {
            SyntaxKind.UnaryMinusExpression => UnOp.Neg,
            SyntaxKind.LogicalNotExpression => UnOp.Not,
            SyntaxKind.BitwiseNotExpression => UnOp.BitNot,
            SyntaxKind.UnaryPlusExpression => (UnOp?)null,
            _ => null,
        };

        if (node.IsKind(SyntaxKind.UnaryPlusExpression)) return Lower(node.Operand);
        if (node.IsKind(SyntaxKind.PreIncrementExpression))
            return Step(node.Operand, BinOp.Add, before: false, loc);
        if (node.IsKind(SyntaxKind.PreDecrementExpression))
            return Step(node.Operand, BinOp.Sub, before: false, loc);
        if (op is null) return Unsupported(node, loc);
        return new IrUnary(loc, op.Value, Lower(node.Operand));
    }

    /// <summary>
    /// R13.3. Lowers <c>x++</c>, <c>++x</c>, <c>x--</c> and <c>--x</c> in expression
    /// position to the write they perform paired with the value they produce.
    ///
    /// A specification is a description of a state, not a thing that runs, so an
    /// increment inside one is meaningless rather than merely unsupported.
    /// </summary>
    private IrExpr Step(ExpressionSyntax operand, BinOp op, bool before, IrLoc loc)
    {
        if (SpecPosition)
        {
            diagnostics.Error("PALCS0576", loc,
                "An increment or decrement cannot appear in a specification, which " +
                "describes a state rather than changing one.");
            return Lower(operand);
        }

        var target = LinearizeLValue(Lower(operand), out var hoisted);
        var stepped = new IrBinary(loc, op, target, new IrLiteral(loc, 1))
            { Type = target.Type, Wraps = Wraps(operand) };
        var write = new IrAssign(loc, target, stepped);
        var name = Fresh("step");
        var snapshot = new IrLocalDecl(loc, name, target.Type ?? stepped.Type!, target)
            { Immutable = true };
        var result = new IrVar(loc, name) { Type = target.Type };

        // Postfix reads before writing; prefix writes before reading. Both take a
        // snapshot, because the operand is a mutable cell whose contents the write
        // changes underneath any later mention of it. The hoisted parts of the L-value
        // come first: they are what the three copies below share.
        var prelude = before
            ? ImmutableArray.CreateRange<IrStmt>([.. hoisted, snapshot, write])
            : ImmutableArray.CreateRange<IrStmt>([.. hoisted, write, snapshot]);
        return new IrStmtExpr(loc, prelude, result) { Type = target.Type };
    }

    /// <summary>R22.14. Whether an assignment target is a <c>[Wrapping]</c> field.</summary>
    public bool Wraps(ExpressionSyntax target) =>
        (model.GetSymbolInfo(target).Symbol is IFieldSymbol f &&
         Declarations.Has(f, known.WrappingAttribute)) || InWrappingMethod(target);

    /// <summary>
    /// <see cref="LinearizeLValue(IrExpr, ImmutableArray{IrStmt}.Builder)"/>, with the
    /// prelude returned rather than appended.
    /// </summary>
    public IrExpr LinearizeLValue(IrExpr lvalue, out ImmutableArray<IrStmt> prelude)
    {
        var builder = ImmutableArray.CreateBuilder<IrStmt>();
        var linear = LinearizeLValue(lvalue, builder);
        prelude = builder.ToImmutable();
        return linear;
    }

    /// <summary>
    /// R21.10. A non-null reference written to a nullable reference variable or
    /// returned at one: C# reports no conversion, nullability being an annotation on
    /// reference types, but the images differ, <c>T</c> and <c>option T</c>; the
    /// conversion is <c>Some</c>.
    /// </summary>
    public IrExpr ToDeclared(IrExpr value, IrType? declared) =>
        declared is IrOptionType option && value is not IrNull &&
        value.Type is { } type and not IrOptionType && type.Equals(option.Inner)
            ? new IrOptionOp(value.Loc, OptionOpKind.Some, value) { Type = option }
            : value;

    /// <summary>
    /// R20.11. A read through a nullable reference is a read through its value: the
    /// <c>option</c> is unwrapped with <c>Some?.v</c>, whose refinement makes F* prove the
    /// reference non-null where it is read -- which is exactly C#'s
    /// <c>NullReferenceException</c>, ruled out.
    /// </summary>
    private static IrExpr NonNull(IrExpr receiver) =>
        receiver.Type is IrOptionType o
            ? new IrOptionOp(receiver.Loc, OptionOpKind.Value, receiver) { Type = o.Inner }
            : receiver;

    /// <summary>
    /// The receiver of a member named by <paramref name="callee"/>: the expression left of
    /// the dot, or, inside a <c>?.</c>, the non-null value it is testing.
    /// </summary>
    private IrExpr? Receiver(ExpressionSyntax callee) => callee switch
    {
        MemberAccessExpressionSyntax m => Lower(m.Expression),
        MemberBindingExpressionSyntax => _bound,
        _ => null,
    };

    private IrExpr? _bound;
    private ExpressionSyntax? BoundSyntax;

    /// <summary>
    /// R20.11. <c>a?.M</c> evaluates <c>a</c> once, and is <c>null</c> when it is and
    /// <c>a.M</c> otherwise: <c>let t = a in if Some? t then [Some] t.M else None</c>.
    /// The member is evaluated only on the branch where <c>a</c> is not null, so a call in
    /// it runs exactly when C# would run it.
    /// </summary>
    private IrExpr LowerConditionalAccess(ConditionalAccessExpressionSyntax node, IrLoc loc)
    {
        var resultType = known.MapType(model.GetTypeInfo(node).Type);
        var tested = Lower(node.Expression);
        if (tested.Type is not IrOptionType inner || resultType is not IrOptionType result)
            return Unsupported(node, loc);

        var prelude = ImmutableArray.CreateBuilder<IrStmt>();
        var subject = tested;
        if (HasEffect(tested))
        {
            var name = Fresh("access");
            prelude.Add(new IrLocalDecl(loc, name, inner, tested) { Immutable = true });
            subject = new IrVar(loc, name) { Type = inner };
        }

        var (savedBound, savedSyntax) = (_bound, BoundSyntax);
        _bound = new IrOptionOp(loc, OptionOpKind.Value, subject) { Type = inner.Inner };
        BoundSyntax = node.Expression;
        IrExpr member;
        try { member = Lower(node.WhenNotNull); }
        finally { (_bound, BoundSyntax) = (savedBound, savedSyntax); }

        if (member.Type is not IrOptionType)
            member = new IrOptionOp(loc, OptionOpKind.Some, member) { Type = result };
        var conditional = new IrConditional(loc,
            new IrOptionOp(loc, OptionOpKind.HasValue, subject) { Type = new IrPrim(PrimKind.Bool) },
            member,
            new IrNull(loc) { Type = result }) { Type = result };
        return prelude.Count == 0
            ? conditional
            : new IrStmtExpr(loc, prelude.ToImmutable(), conditional) { Type = result };
    }

    private int _steps;
    private string Fresh(string hint) => $"__pal_{hint}{_steps++}";

    /// <summary>
    /// R5.3. <c>x op= e</c> and <c>x++</c> are notations for <c>x = x op e</c>, and that
    /// expansion mentions the L-value <em>twice</em> — three times for the expression form,
    /// which also snapshots it. C# evaluates it exactly once (ECMA-334 §12.21, §12.18.3),
    /// so if any part of the L-value has an effect, the expansion is a different program
    /// from the one that runs, and what is proved is a theorem about that other program.
    ///
    /// <para>The remedy is the one R5.14 already applies to a <c>switch</c> scrutinee: the
    /// effectful part is evaluated once, into an immutable local, and every copy of the
    /// L-value names that local. Only an <em>index</em> is hoisted. An effectful array or
    /// receiver would have to be hoisted as a resource rather than a value — a move, not a
    /// binding — so it is refused instead, per §0 rule 3.</para>
    /// </summary>
    public IrExpr LinearizeLValue(IrExpr lvalue, ImmutableArray<IrStmt>.Builder prelude)
    {
        switch (lvalue)
        {
            case IrElement el:
                return el with
                {
                    Array = Opaque(el.Array, "array"),
                    Index = Hoist(el.Index, prelude),
                };

            case IrField f:
                return f with { Receiver = Opaque(f.Receiver, "receiver") };

            default:
                return Opaque(lvalue, "target");
        }

        // A part that cannot be hoisted must at least not be duplicated.
        IrExpr Opaque(IrExpr part, string what)
        {
            if (!HasEffect(part)) return part;
            diagnostics.Error("PALCS0578", part.Loc,
                $"The {what} of this compound assignment or increment has an effect, and " +
                "R5.3 expands the notation into an assignment that names the L-value twice. " +
                "Evaluating it twice is not the program C# runs, and pal-csharp will not " +
                "translate one program as another. Bind it to a local first.");
            return part;
        }
    }

    /// <summary>
    /// Binds <paramref name="index"/> to a fresh immutable local when it has an effect, so
    /// that the copies of the L-value around it share one evaluation.
    /// </summary>
    private IrExpr Hoist(IrExpr index, ImmutableArray<IrStmt>.Builder prelude)
    {
        if (!HasEffect(index)) return index;

        if (index.Type is not { } type)
        {
            diagnostics.Error("PALCS0578", index.Loc,
                "This index has an effect and no type pal-csharp can bind it at, so R5.3's " +
                "expansion would evaluate it twice. Bind it to a local first.");
            return index;
        }

        var name = Fresh("index");
        prelude.Add(new IrLocalDecl(index.Loc, name, type, index) { Immutable = true });
        return new IrVar(index.Loc, name) { Type = type };
    }

    /// <summary>
    /// Whether evaluating this expression can do something — call a method, run the
    /// prelude of an already-lowered increment, or allocate. Deliberately conservative:
    /// the cost of a false positive is a refusal, and of a false negative a wrong program.
    /// </summary>
    private static bool HasEffect(IrExpr expr) =>
        Subexpressions(expr).Any(e => e is IrCall { Kind: CalleeKind.Method }
                                       or IrStmtExpr or IrNew or IrNewArray or IrRaise);

    private static IEnumerable<IrExpr> Subexpressions(IrExpr expr)
    {
        yield return expr;
        IEnumerable<IrExpr> kids = expr switch
        {
            IrUnary u => [u.Operand],
            IrBinary b => [b.Left, b.Right],
            IrConditional c => [c.Cond, c.Then, c.Else],
            IrElement e => [e.Array, e.Index],
            IrLength l => [l.Array],
            IrField f => [f.Receiver],
            IrNew n => [.. n.Fields.Select(f => f.Value)],
            IrRefArg r => [r.Operand],
            IrCall c => c.Args,
            IrConvert c => [c.Operand],
            IrStmtExpr se => [se.Value],
            IrRaise ra => [ra.Exception],
            IrOptionOp oo => [oo.Operand],
            IrOld o => [o.Operand],
            IrLive l => [l.Operand],
            IrQuantifier q => [q.Body],
            IrNewArray n => [n.Length],
            IrContents c => [c.Array],
            IrSeqOp s => s.Args,
            IrListOp l => l.Args,
            IrSpecOp o => o.Args,
            _ => [],
        };
        foreach (var kid in kids)
            foreach (var r in Subexpressions(kid)) yield return r;
    }

    /// <summary>
    /// R6.10. A <c>ref</c>/<c>out</c>/<c>in</c> argument passes the variable itself, so
    /// the reference must survive lowering; without this the callee would be handed a
    /// snapshot of the value and the write it performs would be lost.
    /// </summary>
    public IrExpr LowerArgument(ArgumentSyntax arg)
    {
        var inner = Lower(arg.Expression);
        if (!arg.RefKindKeyword.IsKind(SyntaxKind.None))
            return new IrRefArg(Locations.From(arg), inner);

        // R20.13. A written parameter is passed by reference, so the argument must be a
        // variable for the write to land in.
        if (!SpecPosition && Declarations.WrittenParameterOf(arg, model, known) is { } written)
        {
            if (inner is not IrVar ||
                model.GetSymbolInfo(arg.Expression).Symbol is not (IParameterSymbol or ILocalSymbol))
            {
                diagnostics.Unsupported(Locations.From(arg),
                    $"An argument to `{written.Name}`, which the callee writes, that is not a " +
                    "local or a parameter (doc/translation.md R20.13)");
                return inner;
            }
            return new IrRefArg(Locations.From(arg), inner);
        }
        return inner;
    }

    /// <summary>
    /// R20.13. <c>x[k] = v</c> through a <c>[SpecOp]</c> indexer setter: <c>x</c> becomes
    /// the setter's function applied to <c>x</c>'s value, <c>k</c> and <c>v</c>. Null when the
    /// assignment is not one.
    /// </summary>
    public IrStmt? SpecIndexerWrite(AssignmentExpressionSyntax node, IrLoc loc)
    {
        if (node.Left is not ElementAccessExpressionSyntax { ArgumentList.Arguments: [var key] } ea ||
            Declarations.SpecSetter(model.GetSymbolInfo(ea).Symbol, known) is not { } setter)
            return null;
        if (!node.IsKind(SyntaxKind.SimpleAssignmentExpression) ||
            ea.Expression is not IdentifierNameSyntax receiverName ||
            model.GetSymbolInfo(receiverName).Symbol is not (IParameterSymbol or ILocalSymbol))
        {
            diagnostics.Unsupported(loc,
                "A write through a `[SpecOp]` indexer whose receiver is not a local or a " +
                "parameter, or by a compound operator (doc/translation.md R20.13)");
            return new IrBlock(loc, []);
        }
        var receiver = Lower(receiverName);
        var update = new IrSpecOp(loc, setter,
            [NonNull(receiver), Lower(key.Expression), Lower(node.Right)])
        { Type = receiver.Type };
        return new IrAssign(loc, receiver, update);
    }

    private IrExpr LowerInvocation(InvocationExpressionSyntax node, IrLoc loc)
    {
        if (model.GetSymbolInfo(node).Symbol is not IMethodSymbol method) return Unsupported(node, loc);

        var args = node.ArgumentList.Arguments;

        if (known.IsPalIntrinsic(method))
            return LowerIntrinsic(method, node, args, loc);

        if (method.ContainingType?.ToDisplayString() == "System.Linq.Enumerable")
            return LowerLinq(method, node, loc);

        // R17.5. The two ways to borrow a window by name. Both are recognised by
        // *shape* -- the name, the argument count, and the fact that the result is a span
        // -- rather than by symbol identity, because `AsSpan` is an extension method on
        // `MemoryExtensions` while `Slice` is an instance method on the span itself, and
        // requiring the frontend to know which is which would make the rule about the BCL
        // rather than about C#.
        if (known.IsAnySpan(method.ReturnType) &&
            node.Expression is MemberAccessExpressionSyntax borrow &&
            LowerBorrow(method, borrow, args, loc) is { } window)
            return window;

        // R17.7. Everything else a span can do -- `CopyTo`, `Fill`, `ToArray`, `TryCopyTo`
        // -- is refused. Each is a real operation with a real Pulse counterpart, and none
        // of them is a *borrow*, which is what §17 is about.
        if (known.IsAnySpan(method.ContainingType) || known.IsAnySpan(method.ReturnType))
            return SpanUnsupported($"Span<T>.{method.Name}", loc);

        // R10.5. The constructors and operations of the ghost inductive types. They are
        // static methods on `SpecList`/`SpecTree`, recognised by containing type so that
        // `using static` and qualification make no difference.
        if (SymbolEqualityComparer.Default.Equals(method.ContainingType, known.SpecListOps))
        {
            var op = method.Name switch
            {
                "Empty" => ListOpKind.Empty,
                "Cons" => ListOpKind.Cons,
                "Append" => ListOpKind.Append,
                "Take" => ListOpKind.Take,
                "Drop" => ListOpKind.Drop,
                "InsertAt" => ListOpKind.InsertAt,
                "RemoveAt" => ListOpKind.RemoveAt,
                "Reverse" => ListOpKind.Reverse,
                _ => (ListOpKind?)null,
            };
            if (op is null) return Unsupported(node, loc);
            return new IrListOp(loc, op.Value, [.. args.Select(a => Lower(a.Expression))]);
        }

        // R11.2/R11.3. A user-declared operation or constructor, recognised by attribute
        // rather than by containing type, so that where the user chose to put it makes no
        // difference. An *instance* operation puts the receiver first, which is the same
        // rule a property already followed — `m.Map.Get(k, 0)` and `m.Map.Count` are the
        // same application with a different number of arguments.
        if (known.SpecOpName(method) is not null || known.SpecCtorName(method) is not null)
        {
            var ops = ImmutableArray.CreateBuilder<IrExpr>();
            if (!method.IsStatic && Receiver(node.Expression) is { } recv)
                ops.Add(NonNull(recv));
            foreach (var a in args) ops.Add(Lower(a.Expression));
            return SpecMember(method, ops.ToImmutable(), node, loc);
        }

        if (Bcl.Models(method))
        {
            var bclReceiver = !method.IsStatic && node.Expression is MemberAccessExpressionSyntax bm
                ? Lower(bm.Expression) : null;
            var bclArgs = args.Select(a => Lower(a.Expression)).ToImmutableArray();
            var constants = args.Select(a => model.GetConstantValue(a.Expression) is { HasValue: true } cv
                ? cv.Value : null).ToImmutableArray();
            if (Bcl.Call(method, bclReceiver, bclArgs, constants, loc, out var refusal) is { } modelled)
                return modelled;
            diagnostics.Error("PALCS0625", loc,
                $"`{Trim(node)}`. {refusal ?? "This use of the member is not modelled."} " +
                "(doc/translation.md R20.10).");
            return new IrLiteral(loc, null);
        }

        var kind = Declarations.KindOf(method, known);
        if (kind is null)
        {
            // R18.1. A method the compilation does not declare has no module and never
            // will, so this is not "not yet supported" — it is outside what a whole-program
            // translator can see, and saying which of the two is the difference between a
            // gap the user can wait for and one they must design around.
            if (method.DeclaringSyntaxReferences.IsEmpty)
            {
                diagnostics.Error("PALCS0592", loc,
                    $"`{method.ContainingType?.Name}.{method.Name}` is declared outside this " +
                    "compilation. pal-csharp translates a whole program: a method emits a module " +
                    "and a call emits an `open` of it (doc/translation.md R2.1, R18.1), so a method " +
                    "whose body it cannot see has no module to call and no contract to trust. " +
                    "Only `Pal.*`, a `[Spec]`/`[Lemma]`, and methods declared in this program " +
                    "can be called.");
                return new IrLiteral(loc, null);
            }
            diagnostics.Unsupported(loc,
                $"A call to `{method.Name}`",
                "Only pal-csharp methods, [Spec] functions and [Lemma]s can be called.");
            return new IrLiteral(loc, null);
        }

        // §4.5. An instance method is emitted as a function whose first binder is the
        // object, so the receiver is lowered as the first argument. A method called with
        // no receiver at all is called on `this`, which is the same node the frontend
        // synthesised as the enclosing method's first parameter.
        //
        // R9.18f. That node carries the *enclosing* class as its type, and for a virtual
        // method the type is the whole content of the call: R9.18 gives every class a
        // forwarder for every method it inherits, and which forwarder to call is read off
        // the receiver's static type, never off the class that declared the member. An
        // untyped `this` falls back to the declaring class, and a call one level up then
        // hands a derived reference to a wrapper expecting a base one. C# writes the same
        // bare `GetArea()` either way, so nothing in the source marks the difference.
        var receiver = method is { IsStatic: false, MethodKind: MethodKind.Ordinary } &&
                       known.HasModel(method.ContainingType!)
            ? node.Expression is MemberAccessExpressionSyntax m && m.Expression is not ThisExpressionSyntax
                ? Lower(m.Expression)
                : new IrVar(loc, Names.This) { Type = Enclosing(node) }
            : null;

        // R20.12. A receiver-free callee is passed the receiver's readonly fields it reads.
        // Only a receiver-free caller has them to pass, and only for its own receiver.
        var context = ImmutableArray<ISymbol>.Empty;
        if (Declarations.IsReceiverFree(method, known) &&
            Declarations.ContextFields(method.ContainingType!, model.Compilation, known) is { IsEmpty: false } fields)
        {
            var onThis = node.Expression is IdentifierNameSyntax or GenericNameSyntax ||
                         node.Expression is MemberAccessExpressionSyntax { Expression: ThisExpressionSyntax };
            if (!onThis || model.GetEnclosingSymbol(node.SpanStart) is not IMethodSymbol caller ||
                !Declarations.IsReceiverFree(caller, known) ||
                !SymbolEqualityComparer.Default.Equals(caller.ContainingType, method.ContainingType))
            {
                diagnostics.Unsupported(loc,
                    $"A call to `{method.Name}`, which reads fields of its receiver, from outside a " +
                    "receiver-free method of the same object (doc/translation.md R20.12)");
                return new IrLiteral(loc, null);
            }
            context = fields;
        }

        return new IrCall(loc, Naming.Of(method),
            receiver is null
                ? [.. args.Select(LowerArgument), .. context.Select(ContextRead)]
                : [receiver, .. args.Select(LowerArgument)])
        {
            Kind = kind.Value,
            ResultType = known.MapType(method.ReturnType),
            HasReceiver = receiver is not null,
            ParamTypes = [.. Declarations.ParamTypes(method, known, receiver is not null),
                          .. context.Select(f => (IrType?)known.MapType(Declarations.ContextType(f)))],
            TypeArguments = known.TypeArguments(method),
            MutatesReceiver = receiver is not null && !Declarations.IsReadOnly(method, model.Compilation),
            DoesNotReturn = method.GetAttributes().Any(a => a.AttributeClass?.ToDisplayString() ==
                "System.Diagnostics.CodeAnalysis.DoesNotReturnAttribute"),
        };
    }

    /// <summary>
    /// R9.18f. The class whose method is being lowered, as the type of a synthesised
    /// <c>this</c>. Read from the position rather than from the callee, because the callee
    /// may have been declared several levels up.
    /// </summary>
    private IrType? Enclosing(SyntaxNode node) =>
        model.GetEnclosingSymbol(node.SpanStart)?.ContainingType is { } self && known.HasModel(self)
            ? known.MapType(self) ?? new IrClassType(self.Name)
            : null;

    /// <summary>R20.5. The hidden counter of the <c>foreach</c> over <paramref name="variable"/>.</summary>
    public static string ForEachIndex(string variable) => variable + "__index";

    /// <summary>
    /// R20.6. <c>src.OrderBy(x =&gt; x.P).ToList()</c>, where <c>P</c> is a
    /// <c>[SpecOp]</c> member: a stable sort, as <c>Pulse.Lib.CSharp.Linq.order_by_to_list</c>.
    /// Every other LINQ operator is refused.
    /// </summary>
    private IrExpr LowerLinq(IMethodSymbol method, InvocationExpressionSyntax node, IrLoc loc)
    {
        if (method.Name == "ToList" && Key(node) is { } k &&
            node.Expression is MemberAccessExpressionSyntax
            {
                Expression: InvocationExpressionSyntax { Expression: MemberAccessExpressionSyntax src },
            } &&
            known.MapType(model.GetTypeInfo(src.Expression).Type) is IrArrayType)
            return new IrOrderBy(loc, Lower(src.Expression), k.Key, k.Type);

        diagnostics.Error("PALCS0622", loc,
            $"`{Trim(node)}`. The only LINQ translated is `src.OrderBy(x => x.P).ToList()` over " +
            "an array or a list, where `P` is a `[SpecOp]` member of integer or decimal type " +
            "(doc/translation.md R20.6).");
        return new IrLiteral(loc, null);
    }

    private (string Key, IrType Type)? Key(InvocationExpressionSyntax toList)
    {
        if (toList.Expression is not MemberAccessExpressionSyntax { Expression: InvocationExpressionSyntax inner }) return null;
        if (model.GetSymbolInfo(inner).Symbol is not IMethodSymbol { Name: "OrderBy" } ob ||
            ob.ContainingType?.ToDisplayString() != "System.Linq.Enumerable") return null;
        if (inner.ArgumentList.Arguments.Count != 1 ||
            inner.ArgumentList.Arguments[0].Expression is not SimpleLambdaExpressionSyntax
            {
                Body: MemberAccessExpressionSyntax { Expression: IdentifierNameSyntax v } access,
            } lambda ||
            v.Identifier.ValueText != lambda.Parameter.Identifier.ValueText) return null;
        if (model.GetSymbolInfo(access).Symbol is not IPropertySymbol prop ||
            known.SpecOpName(prop) is not { } key) return null;
        if (known.MapType(prop.Type) is not IrPrim { Kind: PrimKind.Decimal or PrimKind.Int or PrimKind.Long } t) return null;
        return (key, t);
    }

    private IrExpr LowerIntrinsic(
        IMethodSymbol method, InvocationExpressionSyntax node,
        SeparatedSyntaxList<ArgumentSyntax> args, IrLoc loc)
    {
        IrExpr Arg(int i) => Lower(args[i].Expression);

        switch (method.Name)
        {
            case nameof(PalLang.Pal.Old): return new IrOld(loc, Arg(0));
            case nameof(PalLang.Pal.Result): return new IrResult(loc);
            case nameof(PalLang.Pal.Live): return new IrLive(loc, Arg(0));
            case nameof(PalLang.Pal.Implies): return new IrBinary(loc, BinOp.Implies, Arg(0), Arg(1));
            case nameof(PalLang.Pal.Iff): return new IrBinary(loc, BinOp.Iff, Arg(0), Arg(1));
            // R15.6. The same equality `==` denotes everywhere else in spec position.
            case nameof(PalLang.Pal.Same): return new IrBinary(loc, BinOp.Eq, Arg(0), Arg(1));
            case nameof(PalLang.Pal.Contents): return new IrContents(loc, Arg(0));
            // R20.5. The position of a `foreach` iteration variable: the loop's counter.
            case nameof(PalLang.Pal.Index):
                if (args[0].Expression is IdentifierNameSyntax iter &&
                    model.GetSymbolInfo(iter).Symbol is ILocalSymbol local &&
                    local.DeclaringSyntaxReferences.FirstOrDefault()?.GetSyntax() is ForEachStatementSyntax)
                    return new IrVar(loc, ForEachIndex(local.Name)) { Type = IrPrim.Int };
                diagnostics.Error("PALCS0621", loc,
                    "`Pal.Index` names the iteration variable of an enclosing `foreach` " +
                    "(doc/translation.md R20.5).");
                return new IrLiteral(loc, null);
            case nameof(PalLang.Pal.IsPermutation):
                return new IrSeqOp(loc, SeqOpKind.IsPermutation, [Arg(0), Arg(1)]);
            case nameof(PalLang.Pal.SetAt):
                return new IrSeqOp(loc, SeqOpKind.SetAt, [Arg(0), Arg(1), Arg(2)]);
            case nameof(PalLang.Pal.Slice):
                return new IrSeqOp(loc, SeqOpKind.Slice, [Arg(0), Arg(1), Arg(2)]);
            case nameof(PalLang.Pal.Snoc):
                return new IrSeqOp(loc, SeqOpKind.Snoc, [Arg(0), Arg(1)]);
            case nameof(PalLang.Pal.Concat):
                return new IrSeqOp(loc, SeqOpKind.Concat, [Arg(0), Arg(1)]);
            case nameof(PalLang.Pal.EmptySeq):
                return new IrSeqOp(loc, SeqOpKind.Empty, []);
            // R17.8. What a parent holds after a window is given back.
            case nameof(PalLang.Pal.Splice):
                return new IrSeqOp(loc, SeqOpKind.Splice, [Arg(0), Arg(1), Arg(2), Arg(3)]);
            case nameof(PalLang.Pal.Rotate):
                return new IrSeqOp(loc, SeqOpKind.Rotate, [Arg(0), Arg(1)]);
            case nameof(PalLang.Pal.Forall) or nameof(PalLang.Pal.Exists):
                return LowerQuantifier(method.Name == nameof(PalLang.Pal.Forall), args, loc);
            case nameof(PalLang.Pal.InlinePulse) when ConstantString(args[0].Expression) is { } text:
                return new IrInlinePulse(loc, text);
            default:
                diagnostics.Unsupported(loc, $"`Pal.{method.Name}` in this position");
                return new IrLiteral(loc, null);
        }
    }

    private IrExpr LowerQuantifier(
        bool isForall, SeparatedSyntaxList<ArgumentSyntax> args, IrLoc loc)
    {
        if (args.Count != 1 || args[0].Expression is not ParenthesizedLambdaExpressionSyntax lambda)
        {
            diagnostics.Unsupported(loc, "A quantifier whose body is not a lambda",
                "Write `Pal.Forall((int i) => ...)`.");
            return new IrLiteral(loc, null);
        }

        var binders = ImmutableArray.CreateBuilder<IrBinder>();
        foreach (var p in lambda.ParameterList.Parameters)
        {
            var symbol = model.GetDeclaredSymbol(p);
            var type = known.MapType(symbol?.Type);
            if (type is null)
            {
                diagnostics.Unsupported(Locations.From(p), $"The quantifier binder type `{p.Type}`");
                type = IrPrim.SpecIntType;
            }
            binders.Add(new IrBinder(p.Identifier.ValueText, type));
        }

        if (lambda.ExpressionBody is null)
        {
            diagnostics.Unsupported(loc, "A quantifier with a statement body",
                "The body must be a single expression.");
            return new IrLiteral(loc, null);
        }

        return new IrQuantifier(loc, isForall, binders.ToImmutable(), Lower(lambda.ExpressionBody));
    }

    public string? ConstantString(ExpressionSyntax expression) =>
        model.GetConstantValue(expression) is { HasValue: true, Value: string s } ? s : null;
}
