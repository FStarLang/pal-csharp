using System.Collections.Immutable;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using Pal.Compiler.Diagnostics;
using Pal.Compiler.Ir;

namespace Pal.Compiler.Frontend;

/// <summary>
/// §19. Exception classes. An exception class is a class the program declares that
/// derives from <c>System.Exception</c>; it becomes an F* <c>exception</c> whose payload
/// is a record of its fields (R19.1).
/// </summary>
public static partial class FrontendPass
{
    private static ImmutableArray<IrException> CollectExceptions(
        CSharpCompilation compilation, WellKnown known, DiagnosticBag diagnostics)
    {
        var symbols = new List<INamedTypeSymbol>();
        foreach (var tree in compilation.SyntaxTrees)
        {
            var model = compilation.Model(tree);
            foreach (var decl in tree.GetRoot().DescendantNodes().OfType<ClassDeclarationSyntax>())
                if (model.GetDeclaredSymbol(decl) is INamedTypeSymbol s && known.IsExceptionClass(s))
                    symbols.Add(s);
        }

        // Bases first, so that a subclass's constructor can read the mapping its base's
        // constructor established.
        var done = new Dictionary<INamedTypeSymbol, IrException>(SymbolEqualityComparer.Default);
        var result = ImmutableArray.CreateBuilder<IrException>();
        foreach (var s in symbols.OrderBy(Depth).ThenBy(s => s.Name, StringComparer.Ordinal))
        {
            if (done.ContainsKey(s)) continue;
            // R20.1b. Under `[TranslateAnnotatedOnly]` an exception class whose payload does
            // not translate is not refused: like any class the annotations do not reach, it
            // is simply not translated, and a use of it in translated code is refused there.
            var bag = known.AnnotatedOnly ? new DiagnosticBag() : diagnostics;
            var lowered = LowerException(compilation, s, known, done, bag);
            if (known.AnnotatedOnly && bag.HasErrors)
            {
                known.SkipException(s);
                continue;
            }
            foreach (var d in bag == diagnostics ? [] : bag.Items) diagnostics.Add(d);
            if (lowered is null) continue;
            done[s] = lowered;
            result.Add(lowered);
        }
        return result.ToImmutable();

        static int Depth(INamedTypeSymbol s)
        {
            var d = 0;
            for (var t = s.BaseType; t is not null; t = t.BaseType) d++;
            return d;
        }
    }

    private static IrException? LowerException(
        CSharpCompilation compilation, INamedTypeSymbol symbol, WellKnown known,
        IReadOnlyDictionary<INamedTypeSymbol, IrException> done, DiagnosticBag diagnostics)
    {
        var loc = Locations.From(symbol.Locations.FirstOrDefault() ?? Location.None);

        if (symbol.TypeParameters.Length > 0)
        {
            diagnostics.Error("PALCS0610", loc,
                $"The exception class `{symbol.Name}` is generic. F*'s `exception` declarations " +
                "are monomorphic, so an exception class must be too (doc/translation.md R19.1).");
            return null;
        }

        IrException? parent = null;
        if (symbol.BaseType is { } b && !known.IsSystemException(b))
        {
            if (!done.TryGetValue(b, out parent))
            {
                diagnostics.Error("PALCS0610", loc,
                    $"The exception class `{symbol.Name}` derives from `{b.Name}`, which is " +
                    "neither `System.Exception` nor an exception class this program declares. " +
                    "Its fields would be part of the payload, and they are not visible to the " +
                    "translator (doc/translation.md R19.1).");
                return null;
            }
        }

        // R19.1. The payload: get-only auto-properties and readonly fields.
        var own = ImmutableArray.CreateBuilder<IrFieldDecl>();
        foreach (var member in symbol.GetMembers())
        {
            if (member.IsStatic || member.IsImplicitlyDeclared) continue;
            ITypeSymbol? type = null;
            switch (member)
            {
                case IPropertySymbol { SetMethod: null } p when IsAuto(p):
                    type = p.Type;
                    break;
                case IFieldSymbol { IsReadOnly: true, AssociatedSymbol: null } f:
                    type = f.Type;
                    break;
                case IPropertySymbol or IFieldSymbol:
                    diagnostics.Error("PALCS0611", Locations.From(member.Locations[0]),
                        $"`{symbol.Name}.{member.Name}` is not a get-only auto-property or a " +
                        "readonly field. An exception's payload is immutable: it is an F* value " +
                        "carried by the exception, not an object (doc/translation.md R19.1).");
                    continue;
                default:
                    continue;
            }
            var mapped = known.MapType(type);
            if (mapped is null or IrArrayType or IrSpanType or IrClassType or IrExnType
                || mapped is IrPrim { Kind: PrimKind.SlProp })
            {
                diagnostics.Error("PALCS0611", Locations.From(member.Locations[0]),
                    $"The exception field `{symbol.Name}.{member.Name}` has type `{type}`. A " +
                    "payload field must be a value: a primitive, a struct or a specification " +
                    "type, not a resource (doc/translation.md R19.1).");
                continue;
            }
            own.Add(new IrFieldDecl(Locations.From(member.Locations[0]), member.Name, mapped));
        }

        var fields = (parent?.Fields ?? []).AddRange(own);

        var ctors = symbol.InstanceConstructors.Where(c => !c.IsImplicitlyDeclared).ToList();
        if (ctors.Count > 1)
        {
            diagnostics.Error("PALCS0612", loc,
                $"The exception class `{symbol.Name}` declares {ctors.Count} constructors. " +
                "pal-csharp translates one, as the function that builds the payload " +
                "(doc/translation.md R19.1).");
            return null;
        }

        if (ctors.Count == 0)
        {
            // The implicit constructor calls `base()` and sets nothing.
            var baseInits = parent is null ? [] :
                parent.Ctor is { Length: 0 } ? parent.Inits : default(ImmutableArray<IrExpr>?);
            if (baseInits is null || own.Count > 0)
            {
                if (!symbol.IsAbstract)
                    diagnostics.Error("PALCS0612", loc,
                        $"The exception class `{symbol.Name}` has fields but no constructor to " +
                        "set them (doc/translation.md R19.1).");
                return new IrException(loc, symbol.Name, parent?.Name, fields, null, [])
                { IsAbstract = true };
            }
            return new IrException(loc, symbol.Name, parent?.Name, fields, [], baseInits.Value)
            { IsAbstract = symbol.IsAbstract };
        }

        var ctor = ctors[0];
        if (ctor.DeclaringSyntaxReferences.FirstOrDefault()?.GetSyntax()
            is not ConstructorDeclarationSyntax syntax)
            return null;
        var model = compilation.Model(syntax.SyntaxTree);
        var parameters = LowerParameters(ctor, model, known, diagnostics);
        var lowerer = new ExprLowerer(model, known, diagnostics, specPosition: false);
        var paramNames = new HashSet<string>(ctor.Parameters.Select(p => p.Name));

        IrExpr? Simple(ExpressionSyntax e)
        {
            var lowered = lowerer.Lower(e);
            if (lowered is IrLiteral || lowered is IrVar v && paramNames.Contains(v.Name)) return lowered;
            diagnostics.Error("PALCS0613", Locations.From(e),
                $"`{e}` in the constructor of `{symbol.Name}`. An exception constructor may " +
                "pass on only its parameters and literals: it is translated to a pure function " +
                "that builds the payload (doc/translation.md R19.1).");
            return null;
        }

        var inits = new IrExpr?[fields.Length];
        var inherited = parent?.Fields.Length ?? 0;

        if (parent is not null)
        {
            if (parent.Ctor is not { } baseParams)
            {
                diagnostics.Error("PALCS0612", loc,
                    $"`{symbol.Name}` derives from `{parent.Name}`, which has no constructor " +
                    "pal-csharp could translate (doc/translation.md R19.1).");
                return null;
            }
            var args = syntax.Initializer is { ThisOrBaseKeyword.ValueText: "base" } init
                ? init.ArgumentList.Arguments.Select(a => Simple(a.Expression)).ToList()
                : [];
            if (args.Count != baseParams.Length || args.Any(a => a is null))
            {
                if (args.All(a => a is not null))
                    diagnostics.Error("PALCS0613", loc,
                        $"The constructor of `{symbol.Name}` must call `base(…)` with every " +
                        $"parameter of `{parent.Name}`'s constructor (doc/translation.md R19.1).");
                return null;
            }
            var subst = baseParams.Select((p, i) => (p.Name, Arg: args[i]!))
                .ToDictionary(x => x.Name, x => x.Arg);
            for (var i = 0; i < inherited; i++)
                inits[i] = parent.Inits[i] is IrVar pv && subst.TryGetValue(pv.Name, out var a)
                    ? a : parent.Inits[i];
        }
        else if (syntax.Initializer is { ThisOrBaseKeyword.ValueText: "this" })
        {
            diagnostics.Error("PALCS0613", loc,
                $"The constructor of `{symbol.Name}` delegates with `this(…)` (doc/translation.md R19.1).");
            return null;
        }
        // A `base(…)` call on System.Exception passes a message and an inner exception,
        // which are not modelled (R19.1); their arguments are not evaluated by the
        // translation, so they must have no effect.
        else if (syntax.Initializer is { } sysInit)
        {
            foreach (var a in sysInit.ArgumentList.Arguments)
            {
                if (a.Expression is IdentifierNameSyntax or LiteralExpressionSyntax) continue;
                diagnostics.Error("PALCS0613", Locations.From(a),
                    $"`{a}` is passed to `System.Exception`'s constructor. Its message is not " +
                    "modelled, so the argument must be a parameter or a literal " +
                    "(doc/translation.md R19.1).");
            }
        }

        var statements = syntax.Body?.Statements.ToList()
            ?? (syntax.ExpressionBody is { } eb
                ? [SyntaxFactory.ExpressionStatement(eb.Expression)]
                : []);
        foreach (var st in statements)
        {
            if (st is ExpressionStatementSyntax
                {
                    Expression: AssignmentExpressionSyntax
                    {
                        RawKind: (int)SyntaxKind.SimpleAssignmentExpression,
                    } assign,
                }
                && Target(assign.Left) is { } name
                && own.Select((f, i) => (f, i)).FirstOrDefault(x => x.f.Name == name) is { f: not null } hit)
            {
                if (inits[inherited + hit.i] is not null)
                    diagnostics.Error("PALCS0613", Locations.From(st),
                        $"`{symbol.Name}.{name}` is assigned twice (doc/translation.md R19.1).");
                inits[inherited + hit.i] = Simple(assign.Right);
                continue;
            }
            diagnostics.Error("PALCS0613", Locations.From(st),
                $"`{st}` in the constructor of `{symbol.Name}`. An exception constructor may " +
                "only assign its own fields (doc/translation.md R19.1).");
            return null;
        }

        for (var i = inherited; i < fields.Length; i++)
        {
            if (inits[i] is not null) continue;
            diagnostics.Error("PALCS0613", loc,
                $"The constructor of `{symbol.Name}` does not set `{fields[i].Name}` " +
                "(doc/translation.md R19.1).");
            return null;
        }
        if (inits.Any(x => x is null)) return null;

        return new IrException(loc, symbol.Name, parent?.Name, fields, parameters, [.. inits!])
        { IsAbstract = symbol.IsAbstract };

        static string? Target(ExpressionSyntax e) => e switch
        {
            IdentifierNameSyntax id => id.Identifier.ValueText,
            MemberAccessExpressionSyntax { Expression: ThisExpressionSyntax, Name: var n } => n.Identifier.ValueText,
            _ => null,
        };

        static bool IsAuto(IPropertySymbol p) =>
            p.DeclaringSyntaxReferences.FirstOrDefault()?.GetSyntax() is PropertyDeclarationSyntax
            {
                ExpressionBody: null,
                Initializer: null,
                AccessorList: { } list,
            } && list.Accessors.All(a => a.Body is null && a.ExpressionBody is null);
    }
}
