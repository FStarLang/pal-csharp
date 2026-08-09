using System.Collections.Immutable;
using Pal.Compiler.Emit;
using Pal.Compiler.Ir;

namespace Pal.Compiler.Frontend;

/// <summary>
/// R9.21. Desugars a concrete class that is not <c>sealed</c> into the two halves §9
/// already translates: an <c>abstract</c> class carrying the contracts, and a generated
/// <c>sealed</c> leaf carrying the representation and the bodies.
///
/// <para>The rewrite is entirely at the IR level, which is what keeps it honest about
/// locations: a body replicated into a second leaf is the <em>same</em> IR, so the
/// <c>IrLoc</c> it reports is the one place the user wrote it. A syntax-level rewrite
/// would have had to invent positions in a file that does not exist.</para>
///
/// <para>Flattening runs before splitting, base-first. A subclass's inherited fields
/// belong to its <em>leaf</em>, and after the split the leaf is not the class the base
/// list names, so the two orders are not interchangeable.</para>
/// </summary>
internal static class OpenClasses
{
    /// <summary>The suffix of the leaf generated for an open class's own instances.</summary>
    public const string ImplSuffix = "__impl";

    public static void Desugar(ImmutableArray<IrDecl>.Builder declarations)
    {
        var classes = declarations.OfType<IrClass>().ToList();
        if (!classes.Any(c => c.IsOpen)) return;

        var byName = classes.ToDictionary(c => c.Name);
        foreach (var d in classes.OrderBy(c => Depth(c, byName)))
        {
            if (d.BaseClass is not { } b || !byName.TryGetValue(b, out var parent)) continue;
            if (!parent.IsOpen) continue;
            // `byName` is re-read rather than captured: a class flattened earlier in this
            // loop is the one a grandchild must inherit from, fields and all.
            Flatten(byName[d.Name], byName[b], declarations, byName);
        }

        foreach (var c in byName.Values.Where(c => c.IsOpen).ToList())
            Split(c, declarations);
    }

    /// <summary>How many translated classes lie between this one and the root.</summary>
    private static int Depth(IrClass c, Dictionary<string, IrClass> byName)
    {
        var n = 0;
        for (var at = c.BaseClass; at is not null && byName.TryGetValue(at, out var up); at = up.BaseClass)
            if (++n > byName.Count) break;
        return n;
    }

    /// <summary>
    /// R9.21b. A subclass of an open class inherits its base's representation and every
    /// body the base declared that it does not override.
    ///
    /// <para>R9.2 gives the abstract half no fields, so "inherits" has to be made true by
    /// replication: what C# resolves by walking a base chain at run time, the scheme
    /// resolves by giving each leaf the whole of what it is. The base's invariant travels
    /// with its fields, for the same reason — it is the only thing that says what they
    /// mean — and so does its abstraction function, because C# offers a subclass no way to
    /// write one of its own over a representation it did not declare.</para>
    /// </summary>
    private static void Flatten(
        IrClass d, IrClass parent, ImmutableArray<IrDecl>.Builder declarations,
        Dictionary<string, IrClass> byName)
    {
        // The fields themselves were inherited at collection time, where the abstraction
        // function that reads them could still be lowered. What is left is the invariant
        // over them: already lowered, in the base's own context, and valid here because
        // the subclass now has the very fields it names.
        var flattened = d with { Invariants = [.. parent.Invariants, .. d.Invariants] };
        for (var i = 0; i < declarations.Count; i++)
            if (ReferenceEquals(declarations[i], d)) declarations[i] = flattened;
        byName[d.Name] = flattened;

        // R9.21c. `D(…) : base(args)` builds one object, not two: the base half of D's
        // representation is initialised by the base's own constructor body, which is
        // inlined here. R4.12c's reading of `: this(args)` -- that the chained constructor
        // *is* the result -- is exactly what does not hold of `base`, because the base's
        // constructor builds the base's leaf and D is not it.
        for (var i = 0; i < declarations.Count; i++)
        {
            if (declarations[i] is not IrMethod
                { IsConstructor: true, DeclaringClass: { } who } ctor || who != d.Name) continue;
            if (Chained(ctor) is not { } call) continue;
            if (declarations.OfType<IrMethod>().FirstOrDefault(
                    m => m.IsConstructor && m.Name == call.Callee) is not { Body: { } up } based)
                continue;

            // The arguments are bound *under the base constructor's parameter names* rather
            // than substituted into its body: a renaming needs no traversal of the
            // expressions it would otherwise have to rewrite, and cannot get one wrong.
            var prologue = based.Parameters
                .Where(p => p.Name != Names.This)
                .Zip(call.Args, (p, arg) => (IrStmt)new IrLocalDecl(call.Loc, p.Name, p.Type, arg));
            declarations[i] = ctor with
            {
                Body = new IrBlock(ctor.Loc, [
                    .. prologue,
                    .. Statements(up),
                    .. Statements(ctor.Body).Skip(1)]),
            };
        }

        var mine = new HashSet<string>(
            declarations.OfType<IrMethod>().Where(m => m.DeclaringClass == d.Name).Select(Member),
            StringComparer.Ordinal);

        // Every body the subclass did not write for itself. The IR is shared, so the
        // replica reports at the line the user wrote the body on — which is where a
        // failure in it is, whichever leaf it was checked in.
        foreach (var m in declarations.OfType<IrMethod>().ToList())
        {
            if (m.DeclaringClass != parent.Name || m.IsConstructor || m.IsLemma) continue;
            if (mine.Contains(Member(m))) continue;
            declarations.Add(m with
            {
                Name = d.Name + "_" + Member(m),
                DeclaringClass = d.Name,
                Overrides = parent.Name,
                Parameters = Receiver(m, d.Name),
                // R9.7. The contract belongs to the declaration this replica fills.
                Requires = [],
                Ensures = [],
                Preserves = [],
            });
        }
    }

    /// <summary>
    /// Replaces <paramref name="c"/> with its abstract half and adds the leaf that stands
    /// for <c>new C(…)</c>. A method <em>declared</em> here becomes an <c>abstract</c>
    /// declaration on the abstract half — where R9.7 says its contract belongs — and an
    /// <c>override</c> carrying the body on the leaf. A method that is already an override
    /// fills a slot that exists further up, so it only moves.
    /// </summary>
    private static void Split(IrClass c, ImmutableArray<IrDecl>.Builder declarations)
    {
        var leafName = c.Name + ImplSuffix;

        // R9.2. The representation, the invariant over it and the abstraction function all
        // belong to the leaf; the model *type* and its refinement belong to both, because
        // the base's own model is what a client of the base reasons about.
        var half = c with
        {
            Fields = [],
            ModelBody = null,
            Invariants = [],
            IsAbstract = true,
            IsOpen = false,
            Recursion = null,
        };
        var leaf = new IrClass(
            c.Loc, leafName, c.Fields, c.ModelMember, c.ModelType, c.ModelBody,
            c.ModelRefinements, c.Invariants, [])
        {
            BaseClass = c.Name,
            IsAbstract = false,
            // R9.6. The leaf adds nothing to what its own abstract half knows, so the
            // forgetting function is the identity — which R9.15e made survivable.
            ForgetBody = null,
            TypeParameters = c.TypeParameters,
            Recursion = c.Recursion,
            IsPlain = c.IsPlain,
        };

        for (var i = 0; i < declarations.Count; i++)
        {
            if (ReferenceEquals(declarations[i], c)) { declarations[i] = half; continue; }
            if (declarations[i] is not IrMethod { DeclaringClass: { } owner } m ||
                owner != c.Name) continue;

            // A constructor keeps its name and its declared return type, so every `new C(…)`
            // in the program is untouched: it really does yield a `C`. What changes is what
            // it builds — the leaf — and R9.21a upcasts the result before returning it.
            if (m.IsConstructor)
            {
                declarations[i] = m with
                {
                    DeclaringClass = leafName,
                    ConstructsLeaf = leafName,
                    Parameters = Receiver(m, leafName),
                };
                continue;
            }
            // A lemma is pure and has no representation to run against, so it stays where
            // the user wrote it.
            if (m.IsLemma) continue;

            var moved = m with
            {
                Name = leafName + "_" + Member(m),
                DeclaringClass = leafName,
                // R9.14 reads `Overrides` as the *immediate* base whose view the receiver
                // arrives under, not the class that first declared the slot. The leaf's
                // immediate base is its own abstract half, whatever the method overrode
                // in the source.
                Overrides = c.Name,
                // The body runs against the leaf's representation, so its receiver is a
                // leaf. The *contract* stays at the base's model, which is what R9.7's
                // `Overrides` says and R9.15e's bracket then arranges.
                Parameters = Receiver(m, leafName),
                // R9.7. The contract was written once, on the declaration this fills.
                // `InheritContracts` runs after this pass and puts it back.
                Requires = [],
                Ensures = [],
                Preserves = [],
            };

            // An `override` fills a slot declared further up, and §9.9 never re-declares
            // one: an abstract class in the middle of a chain leaves its base's abstract
            // methods alone. So the body only moves, and the half declares nothing.
            if (m.Overrides is not null) { declarations[i] = moved; continue; }

            declarations[i] = m with { IsAbstract = true, Body = null, PulseBody = null };
            declarations.Add(moved);
        }

        declarations.Add(leaf);
    }

    /// <summary>The call to a base constructor a constructor body opens with, if any.</summary>
    private static IrCall? Chained(IrMethod ctor) =>
        Statements(ctor.Body) is [IrExprStmt { Expr: IrCall { Kind: CalleeKind.Method } c }, ..] &&
        c.Callee.EndsWith("__ctor", StringComparison.Ordinal) ? c : null;

    private static ImmutableArray<IrStmt> Statements(IrStmt? body) =>
        body is IrBlock b ? b.Statements : body is null ? [] : [body];

    /// <summary>
    /// The parameter list with the receiver retyped to the class the body will run in.
    /// R4.10 opens the receiver against its own invariant, so it has to be the leaf that
    /// has one — the abstract half has no representation to open.
    /// </summary>
    private static ImmutableArray<IrParam> Receiver(IrMethod m, string owner) =>
        m.Parameters is [{ Name: Names.This } self, .. var rest]
            ? [self with { Type = new IrClassType(owner) }, .. rest]
            : m.Parameters;

    /// <summary>The member's own name, with <see cref="Naming.Of"/>'s qualifier removed.</summary>
    private static string Member(IrMethod m) =>
        m.DeclaringClass is { } c && m.Name.StartsWith(c + "_", StringComparison.Ordinal)
            ? m.Name[(c.Length + 1)..]
            : m.Name;
}
