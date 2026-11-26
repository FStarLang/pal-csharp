using System.Collections.Immutable;
using Pal.Compiler.Ir;
using Pal.Compiler.Passes;

namespace Pal.Compiler.Emit;

internal static class NominalFactsEmitter
{
    // Export only source-only protocol postconditions expressible in the public
    // observation vocabulary. The installer must still establish every exported
    // fact; this extraction does not assert it or assume a successful cast.
    internal static EmittedModule Emit(IrEnumerableType e, IrClass cls,
        IReadOnlyDictionary<string, IrMethod> methods, SpecEmitter spec)
    {
        var schema = e.Capability!;
        var candidates = schema.Iteration?.Evidence is { } evidence &&
            methods.TryGetValue(evidence, out var proof) ? proof.Ensures : [];
        bool ObservationsOnly(IrExpr expression, ImmutableHashSet<string> bound)
        {
            if (expression is IrObserve { Receiver: IrVar { Name: Names.This } } observation)
                return observation.Class == cls.Name &&
                    (observation.Member == schema.Items || observation.Member == schema.Scalar);
            if (expression is IrVar v) return bound.Contains(v.Name);
            if (expression is IrObserve or IrField or IrRefOf or IrResult or IrOld or
                IrInlinePulse or IrStmtExpr or IrLambdaRef)
                return false;
            if (expression is IrQuantifier q)
                return ObservationsOnly(q.Body, bound.Union(q.Binders.Select(b => b.Name)));
            return Check.DirectSubexpressions(expression).All(c => ObservationsOnly(c, bound));
        }
        IEnumerable<IrExpr> Conjuncts(IrExpr expr) => expr is IrBinary { Op: BinOp.And } b
            ? Conjuncts(b.Left).Concat(Conjuncts(b.Right)) : [expr];
        var facts = candidates.SelectMany(Conjuncts)
            .Where(f => ObservationsOnly(f, ImmutableHashSet<string>.Empty) &&
                Check.Subexpressions(f).Any(n => n is IrObserve)).ToArray();
        var itemType = (IrSeqType)cls.Observations.Single(o => o.Name == schema.Items).ReturnType;
        var scalarType = cls.Observations.Single(o => o.Name == schema.Scalar).ReturnType;
        var scope = new SpecScope();
        scope.Bind("$projection:" + cls.Name + ":" + schema.Items, new Term("items", TermKind.Seq, itemType));
        scope.Bind("$projection:" + cls.Name + ":" + schema.Scalar, new Term("scalar", MethodPlan.KindOf(scalarType), scalarType));
        var body = facts.Length == 0 ? "True" :
            string.Join(" /\\ ", facts.Select(f => "(" + spec.AsProp(spec.Emit(f, scope)) + ")"));
        var name = "NominalFacts_" + cls.Name;
        var text = $"module {name}\nmodule Seq = FStar.Seq\nmodule I32 = FStar.Int32\n" +
            "module CS = Pulse.Lib.CSharp.Seq\nmodule CA = Pulse.Lib.CSharp.Arith\n" +
            $"let fact {string.Join(" ", cls.TypeParameters.Select(t => $"({Names.TypeParam(t)}:Type0)"))} " +
            $"(items:Seq.seq {Types.Atom(itemType.Element)}) (scalar:{Types.Render(scalarType)}) : prop =\n  {body}\n";
        return new EmittedModule(name, text) {
            Origin = [new Provenance("*", cls.Loc)], Origins = [new LineOrigin(1, cls.Loc)]
        };
    }
}
