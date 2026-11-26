using System.Text;
using Pal.Compiler.Ir;

namespace Pal.Compiler.Emit;

/// <summary>
/// Checked, per-call-site installation. A view owns the retained source and an
/// existential *current* view cell, never the target class invariant.
/// </summary>
internal static class NominalEnumerableEmitter
{
    internal static EmittedModule Emit(IrEnumerationInstallation d, SpecEmitter spec,
        IReadOnlyDictionary<string, IrMethod> methods, IReadOnlyDictionary<string, IrClass> classes)
    {
        if (d.Cursor is not null) return NominalIteratorEmitter.Emit(d, spec, methods, classes);
        var e = d.Enumerable;
        var sb = new StringBuilder();
        void L(string s = "") => sb.AppendLine(s);
        var binders = string.Join(" ", d.TypeParameters.Select(t => $"(#{Names.TypeParam(t)}:Type0)"));
        var typeArgs = string.Join(" ", d.TypeParameters.Select(t => "#" + Names.TypeParam(t)));
        var logical = EnumerableAdapter.Logical(e);
        var savedType = EnumerableAdapter.ModelType(d.Owner);
        var ownerType = Types.Render(d.Owner);
        var viewType = d.View is null ? null : Types.Render(d.View);
        var inv = $"{Names.ClassModule(d.Owner.Name)}.{Names.ClassInv(d.Owner.Name)}";
        var scope = new SpecScope();
        scope.Bind("owner", new Term("(reveal saved)", TermKind.Other, d.Owner));
        if (d.View is not null) scope.Bind("view", new Term("v", TermKind.Other, d.View));
        var items = spec.Emit(d.Items, scope).Text;
        var scalar = spec.Emit(d.Scalar, scope).Text;
        if (e.Capability!.ScalarType is IrPrim { Kind: PrimKind.Bool })
            scalar = $"(Prims.t2b {scalar})";
        L($"module {d.Module}");
        L("#lang-pulse");
        L("open Pulse");
        L("module C = Pulse.Lib.CSharp.Capability");
        L("module E = Pulse.Lib.CSharp.Enumerable.Capability");
        L("module O = Pulse.Lib.CSharp.Enumerable.Observation");
        L("module S = Pulse.Lib.CSharp.Enumerable.Source");
        L("module R = Pulse.Lib.Reference");
        L("module A = Pulse.Lib.CSharp.Array.Base");
        L("module Seq = FStar.Seq");
        L("module I32 = FStar.Int32");
        L("#set-options \"--z3rlimit 10\"");
        var handleType = ownerType;
        var owner = "x";
        if (d.View is not null)
        {
            var explicitBinders = binders.Replace("(#", "(");
            var explicitArgs = string.Join(" ", d.TypeParameters.Select(Names.TypeParam));
            L($"noeq type handle {explicitBinders} = {{ owner:{ownerType}; state:R.ref ({viewType}) }}");
            handleType = $"handle {explicitArgs}";
            owner = "x.owner";
        }
        var vBinder = d.View is null ? "" : $"(v:{viewType})";
        L($"let project {binders} (saved:erased ({savedType})) {vBinder} : GTot ({logical}) =");
        L($"  {{ O.items = {items}; O.scalar = {scalar} }}");
        L($"let owns {binders} (saved:erased ({savedType})) (x:{handleType}) (p:perm) (m:{logical}) : slprop =");
        L($"  {inv} {owner} #p saved **");
        if (d.View is not null)
        {
            L($"  (exists* (v:{viewType}). R.pts_to x.state v **");
            L($"    pure (v.{Names.StructModule(d.View.Name)}.{Names.Field(d.OwnerField!)} == x.owner /\\");
            L($"      Seq.equal m.O.items {items} /\\ m.O.scalar == {scalar}))");
        }
        else L($"  pure (Seq.equal m.O.items {items} /\\ m.O.scalar == {scalar})");
        foreach (var length in d.Matches ? new[] { true, false } : Array.Empty<bool>())
        {
            var name = length ? "length" : "scalar";
            var result = length ? "I32.t" : Types.Render(e.Capability!.ScalarType);
            var law = length ? "I32.v result == Seq.length (reveal m).O.items" : "result == (reveal m).O.scalar";
            var method = length ? d.LengthMethod : d.ScalarMethod;
            var methodArgs = string.Join(" ", (length ? d.LengthTypeArguments : d.ScalarTypeArguments).Select(Types.Atom));
            L($"fn {name} {binders} (saved:erased ({savedType})) (x:{handleType}) (#p:perm) (#m:erased ({logical}))");
            L($"  preserves owns {typeArgs} saved x p m");
            L($"  returns result:{result}");
            L($"  ensures pure ({law})");
            L("{");
            L($"  unfold (owns {typeArgs} saved x p m);");
            if (d.View is not null) L("  with v. _;");
            L($"  let result = {Names.FunctionModule(method)}.{Names.Function(method)} {methodArgs} {owner}{(d.View is null ? "" : " x.state")};");
            if (d.View is not null) L("  with after. _;");
            L($"  fold (owns {typeArgs} saved x p m);");
            L("  result");
            L("}");
        }
        if (d.Matches)
            L($"let api {binders} (saved:erased ({savedType})) = O.make (length {typeArgs} saved) (scalar {typeArgs} saved)");
        L($"let descriptor {binders} (saved:erased ({savedType})) (x:{handleType})");
        L($"  : w:C.descriptor ({logical}) ({EnumerableAdapter.Api(e)}) {{ {(d.Matches ? "" : "not ")}(C.supports w) }} =");
        var installed = d.Matches ? $"(Some (api {typeArgs} saved))" : "None";
        L($"  C.make #({logical}) #({EnumerableAdapter.Api(e)}) ({handleType}) (owns {typeArgs} saved) x {installed}");
        return new EmittedModule(d.Module, sb.ToString()) {
            Origin = [new Provenance("*", d.Items.Loc)],
            Origins = [new LineOrigin(1, d.Items.Loc)]
        };
    }
}
