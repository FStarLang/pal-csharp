using System.Text;
using Pal.Compiler.Ir;

namespace Pal.Compiler.Emit;

// The descriptor contains checked closures over the real factory and iterator
// methods. Its cursor predicate retains the source and every auxiliary owner.
internal static class NominalIteratorEmitter
{
    internal static EmittedModule Emit(IrEnumerationInstallation d, SpecEmitter spec,
        IReadOnlyDictionary<string, IrMethod> methods, IReadOnlyDictionary<string, IrClass> classes)
    {
        var it = d.Cursor!;
        var e = d.Enumerable;
        var text = new StringBuilder();
        void L(string line = "") => text.AppendLine(line);
        var types = string.Join(" ", d.TypeParameters.Select(t => $"(#{Names.TypeParam(t)}:Type0)"));
        var args = string.Join(" ", d.TypeParameters.Select(t => "#" + Names.TypeParam(t)));
        var defaults = string.Join(" ", d.DefaultedTypes.Select(t =>
            $"{{| _:Pulse.Lib.CSharp.Inhabited.has_default {Names.TypeParam(t)} |}}"));
        var binders = types + " " + defaults;
        var explicitTypes = types.Replace("(#", "(");
        var explicitArgs = string.Join(" ", d.TypeParameters.Select(Names.TypeParam));
        var model = EnumerableAdapter.Logical(e);
        var sourceModel = EnumerableAdapter.ModelType(d.Owner);
        var ownerType = Types.Render(d.Owner);
        var viewType = d.View is null ? null : Types.Render(d.View);
        var cursorType = Types.Render(it.Type);
        var sourceType = d.View is null ? ownerType : $"handle {explicitArgs}";
        var source = d.View is null ? "x" : "x.owner";
        var viewBinder = d.View is null ? "" : $"(v:{viewType})";
        var viewArg = d.View is null ? "" : " v";
        var sourceInv = $"{Names.ClassModule(d.Owner.Name)}.{Names.ClassInv(d.Owner.Name)} {source} #p saved";
        string ClassInv(IrClassType c) => $"{Names.ClassModule(c.Name)}.{Names.ClassInv(c.Name)}";
        string Call(string method, IEnumerable<IrType> ts, string values) =>
            $"{Names.FunctionModule(method)}.{Names.Function(method)} {string.Join(" ", ts.Select(Types.Atom))} {values}";
        var scope = new SpecScope();
        scope.Bind("owner", new Term("(reveal saved)", TermKind.Other, d.Owner));
        scope.Bind(SpecEmitter.ReferenceKey("owner"), new Term(source, TermKind.Other, d.Owner));
        if (d.View is not null)
        {
            scope.Bind("view", new Term("v", TermKind.Other, d.View));
            scope.Bind(SpecEmitter.ReferenceKey("view"), new Term("x.state", TermKind.Other, d.View));
        }
        var items = spec.Emit(d.Items, scope).Text;
        var scalar = spec.Emit(d.Scalar, scope).Text;
        if (e.Capability!.ScalarType is IrPrim { Kind: PrimKind.Bool })
            scalar = $"(Prims.t2b {scalar})";
        scope.Bind("cursor", new Term("raw", TermKind.Other, it.Type));
        foreach (var (name, type) in it.SpecTypes) scope.BindType(name, type);
        foreach (var aux in it.Owned)
            scope.Bind(aux.Local, new Term("m_" + aux.Local, TermKind.Other, aux.Type));
        var ready = spec.AsProp(spec.Emit(it.Ready, scope));
        var pending = spec.Emit(it.Pending, scope).Text;
        var current = spec.Emit(it.Current, scope).Text;
        var valid = spec.Emit(it.Valid, scope).Text;

        L($"module {d.Module}");
        L("#lang-pulse");
        L("open Pulse");
        L("module C = Pulse.Lib.CSharp.Capability");
        L("module I = Pulse.Lib.CSharp.Capability.Iterator");
        L("module O = Pulse.Lib.CSharp.Enumerable.Observation");
        L("module API = Pulse.Lib.CSharp.Enumerable.Observation.Iterable");
        L("module D = FStar.Dyn");
        L("module Recover = Pulse.Lib.CSharp.Assumptions");
        L("module R = Pulse.Lib.Reference");
        L("module B = Pulse.Lib.Box");
        L("module A = Pulse.Lib.CSharp.Array.Base");
        L("module Seq = FStar.Seq");
        L("module I32 = FStar.Int32");
        L("#set-options \"--z3rlimit 10\"");
        if (d.View is not null)
            L($"noeq type handle {explicitTypes} = {{ owner:{ownerType}; state:R.ref ({viewType}) }}");
        L($"noeq type cursor_handle {explicitTypes} = {{ cell:B.box ({cursorType});");
        foreach (var aux in it.Owned) L($"  {aux.Local}:{Types.Render(aux.Type)};");
        L("}");

        // Retain each original source-call domain, instead of assuming that an
        // observation or factory is total on every representable source model.
        var obligations = new[] {
            (Name:"length", Method:d.LengthMethod, Types:d.LengthTypeArguments),
            (Name:"scalar", Method:d.ScalarMethod, Types:d.ScalarTypeArguments),
            (Name:"factory", Method:it.Factory.Callee, Types:it.Factory.TypeArguments)
        };
        var admissions = new List<string>();
        foreach (var obligation in obligations)
        {
            var method = methods[obligation.Method];
            var owner = (IrClassType)method.Parameters[0].Type;
            var pre = new SpecScope();
            pre.Bind(method.Parameters[0].Name, new Term("m", TermKind.Other, owner));
            pre.Bind(SpecEmitter.ReferenceKey(method.Parameters[0].Name), new Term("x", TermKind.Other, owner));
            pre.Bind("$permission", new Term("p", TermKind.Other));
            var vp = d.View is null ? null : method.Parameters[1];
            if (vp is not null)
            {
                pre.Bind(vp.Name, new Term("v", TermKind.Other, vp.Type));
                pre.Bind(SpecEmitter.ReferenceKey(vp.Name), new Term("cell", TermKind.Other, vp.Type));
            }
            var ts = string.Join(" ", method.TypeParameters.Select(t => $"({Names.TypeParam(t)}:Type0)"));
            var ds = string.Join(" ", method.DefaultedTypeParameters.Select(t =>
                $"{{| _:Pulse.Lib.CSharp.Inhabited.has_default {Names.TypeParam(t)} |}}"));
            L($"let needs_{obligation.Name} {ts} {ds} (x:{Types.Render(owner)}) (p:perm)");
            L($"  (m:{EnumerableAdapter.ModelType(owner)}) " +
                (vp is null ? "" : $"(cell:R.ref ({Types.Render(vp.Type)})) (v:{Types.Render(vp.Type)}) ") + ": prop =");
            L("  " + (method.Requires.IsEmpty ? "True" :
                string.Join(" /\\ ", method.Requires.Select(r => "(" + spec.AsProp(spec.Emit(r, pre)) + ")"))));
            admissions.Add($"needs_{obligation.Name} {string.Join(" ", obligation.Types.Select(Types.Atom))} {source} p (reveal saved)" +
                (d.View is null ? "" : " x.state v"));
        }
        var fact = EnumerableAdapter.Fact(e, "m.O.items", "m.O.scalar");
        var sourceLaw = $"({fact}) /\\ Seq.equal m.O.items {items} /\\ m.O.scalar == {scalar} /\\ " +
            string.Join(" /\\ ", admissions.Select(a => "(" + a + ")"));
        if (d.View is not null)
            sourceLaw = $"v.{Names.StructModule(d.View.Name)}.{Names.Field(d.OwnerField!)} == x.owner /\\ " + sourceLaw;
        L($"let project {binders} (saved:erased ({sourceModel})) {viewBinder} : GTot ({model}) =");
        L($"  {{ O.items = {items}; O.scalar = {scalar} }}");
        L($"let owns {binders} (saved:erased ({sourceModel})) (x:{sourceType}) (p:perm) (m:{model}) : slprop =");
        L($"  {sourceInv} **");
        L(d.View is null ? $"  pure ({sourceLaw})" :
            $"  (exists* (v:{viewType}). R.pts_to x.state v ** pure ({sourceLaw}))");
        L($"let cursor_owns {binders} (saved:erased ({sourceModel})) (x:{sourceType}) (h:D.dyn)");
        L($"  (p:perm) (m:{model}) (s:I.state {Types.Atom(e.Element)}) : slprop =");
        L($"  exists* (c:cursor_handle {explicitArgs}) (raw:{cursorType}) " +
            (d.View is null ? "" : $"(v:{viewType}) ") +
            string.Join(" ", it.Owned.Select(a => $"(m_{a.Local}:{EnumerableAdapter.ModelType(a.Type)})")) + ".");
        L($"  {sourceInv} ** B.pts_to c.cell raw **");
        if (d.View is not null) L("  R.pts_to x.state v **");
        foreach (var aux in it.Owned) L($"  {ClassInv(aux.Type)} c.{aux.Local} m_{aux.Local} **");
        var ownerPointer = d.View is null ? source : "x.state";
        L($"  pure (h == D.mkdyn c /\\ raw.{Names.StructModule(it.Type.Name)}.{Names.Field(it.OwnerField)} == {ownerPointer} /\\");
        foreach (var aux in it.Owned)
            L($"    raw.{Names.StructModule(it.Type.Name)}.{Names.Field(aux.Field)} == c.{aux.Local} /\\");
        L($"    ({sourceLaw}) /\\ ({ready}) /\\ Seq.equal ({pending}) s.I.pending /\\");
        L($"    Seq.equal ({current}) s.I.current /\\ (({valid}) <==> I.valid s))");

        string Own(string s = "s") => $"cursor_owns {args} saved x h p m {s}";
        var signature = $"{binders} (saved:erased ({sourceModel})) (x:{sourceType})";
        foreach (var length in new[] { true, false })
        {
            var name = length ? "length" : "scalar";
            L($"fn {name} {signature} (#p:perm) (#m:erased ({model}))");
            L($"  preserves owns {args} saved x p m");
            L($"  returns result:{(length ? "I32.t" : Types.Render(e.Capability!.ScalarType))}");
            L($"  ensures pure ({(length ? "I32.v result == Seq.length (reveal m).O.items" : "result == (reveal m).O.scalar")})");
            L("{");
            L($"  unfold (owns {args} saved x p m);");
            if (d.View is not null) L("  with v. _;");
            L($"  let result = {Call(length ? d.LengthMethod : d.ScalarMethod,
                length ? d.LengthTypeArguments : d.ScalarTypeArguments, source + (d.View is null ? "" : " x.state"))};");
            L($"  fold (owns {args} saved x p m);");
            L("  result");
            L("}");
        }
        L($"fn start {signature} (#p:perm) (#m:erased ({model}))");
        L($"  requires owns {args} saved x p m");
        L("  returns h:D.dyn");
        L($"  ensures {Own("(I.initial (O.contents (reveal m)))")}");
        L("{");
        L($"  unfold (owns {args} saved x p m);");
        if (d.View is not null) L("  with v. _;");
        L($"  let raw = {Call(it.Factory.Callee, it.Factory.TypeArguments, source + (d.View is null ? "" : " x.state"))};");
        foreach (var aux in it.Owned) L($"  let {aux.Local} = raw.{Names.StructModule(it.Type.Name)}.{Names.Field(aux.Field)};");
        L("  let cell = B.alloc raw;");
        L("  let c = { cell = cell; " + string.Join(" ", it.Owned.Select(a => $"{a.Local} = {a.Local};")) + " };");
        L("  rewrite (B.pts_to cell raw) as (B.pts_to c.cell raw);");
        foreach (var aux in it.Owned)
            L($"  rewrite each (raw.{Names.StructModule(it.Type.Name)}.{Names.Field(aux.Field)}) as c.{aux.Local};");
        L("  let h = D.mkdyn c;");
        L($"  fold ({Own("(I.initial (O.contents (reveal m)))")});");
        L("  h");
        L("}");
        foreach (var name in new[] { "next", "value", "dispose", "release" })
        {
            var resultType = name == "next" ? "bool" : name == "value" ? Types.Render(e.Element) : "unit";
            var after = name == "next" ? "(I.step (reveal s))" : "s";
            L($"fn {name} {signature} (h:D.dyn) (#p:perm) (#m:erased ({model}))");
            L($"  (#s:erased (I.state {Types.Atom(e.Element)}){(name == "value" ? " { I.valid s }" : "")})");
            L($"  requires {Own()}");
            L($"  returns result:{resultType}");
            L($"  ensures {(name == "release" ? $"owns {args} saved x p m" : Own(after))}" +
                (name == "next" ? " ** pure (result == I.moves s)" :
                 name == "value" ? " ** pure (result == Seq.index (reveal s).I.current 0)" : ""));
            L("{");
            L($"  unfold ({Own()});");
            L("  with c raw" + viewArg + string.Concat(it.Owned.Select(a => " m_" + a.Local)) + ". _;");
            L($"  let actual = Recover.recover #(cursor_handle {explicitArgs}) #(hide c) h;");
            // Rewrite before stateful calls: c is ghost, actual is the concrete
            // handle selected by the existing runtime-fidelity primitive.
            L("  rewrite each c as actual;");
            L("  let current = B.op_Bang actual.cell;");
            if (name == "release")
            {
                foreach (var aux in it.Owned)
                {
                    var cls = classes[aux.Type.Name];
                    L($"  unfold ({ClassInv(aux.Type)} actual.{aux.Local} m_{aux.Local});");
                    L($"  let raw_{aux.Local} = B.op_Bang actual.{aux.Local};");
                    foreach (var field in cls.Fields.Where(f => f.Type is IrArrayType && !f.IsGhost))
                        L($"  A.free raw_{aux.Local}.{Names.ClassModule(aux.Type.Name)}.{Names.Field(field.Name)};");
                    // Any additional owned resource is deliberately left as a
                    // verification obligation, never discarded by drop_.
                    L($"  B.free actual.{aux.Local};");
                }
                L("  B.free actual.cell;");
                L($"  fold (owns {args} saved x p m);");
            }
            else
            {
                var call = name == "next" ? it.Next : name == "value" ? it.Value : it.Dispose;
                var byReference = call.Args.Any(a => a is IrRefArg { Operand: IrVar { Name: "cursor" } });
                if (byReference) L("  B.to_ref_pts_to actual.cell;");
                string Argument(IrExpr a) => a switch {
                    IrVar { Name: "owner" } => source,
                    IrVar { Name: "cursor" } => "current",
                    IrVar v when it.Owned.Any(o => o.Local == v.Name) => "actual." + v.Name,
                    IrRefArg { Operand: IrVar { Name: "cursor" } } => "(B.box_to_ref actual.cell)",
                    IrRefArg { Operand: IrVar { Name: "view" } } => "x.state",
                    IrRefOf { Parameter: "view" } => "x.state",
                    _ => throw new InvalidOperationException($"Unsupported concrete iterator ABI argument: {a}")
                };
                L($"  let result = {Call(call.Callee, call.TypeArguments, string.Join(" ", call.Args.Select(Argument)))};");
                if (byReference) L("  B.to_box_pts_to actual.cell;");
                if (name == "next")
                {
                    var afterScope = new SpecScope(scope);
                    afterScope.Bind("cursor", new Term("after_raw", TermKind.Other, it.Type));
                    var names = new List<string> { "after_raw" };
                    var resources = new List<string> { "B.pts_to actual.cell after_raw" };
                    if (d.View is not null)
                    {
                        afterScope.Bind("view", new Term("after_view", TermKind.Other, d.View));
                        names.Add("after_view");
                        resources.Add("R.pts_to x.state after_view");
                    }
                    foreach (var aux in it.Owned)
                    {
                        var modelName = "after_" + aux.Local;
                        afterScope.Bind(aux.Local, new Term(modelName, TermKind.Other, aux.Type));
                        names.Add(modelName);
                        resources.Add($"{ClassInv(aux.Type)} actual.{aux.Local} {modelName}");
                    }
                    L($"  with {string.Join(" ", names)}. assert ({string.Join(" ** ", resources)});");
                    L($"  I.next_from_observations (reveal s) ({pending}) " +
                        $"({spec.Emit(it.Pending, afterScope).Text}) ({spec.Emit(it.Current, afterScope).Text}) result;");
                }
                L($"  fold ({Own(after)});");
                L("  result");
            }
            L("}");
        }
        L($"let iterator_slots {binders} (saved:erased ({sourceModel}))");
        L($"  : I.slots ({model}) {Types.Atom(e.Element)} ({sourceType}) (owns {args} saved) O.contents =");
        L($"  {{ I.cursor_owns = cursor_owns {args} saved; start = start {args} saved; next = next {args} saved;");
        L($"     value = value {args} saved; dispose = dispose {args} saved; release = release {args} saved }}");
        L($"fn facts {signature} (#p:perm) (#m:erased ({model}))");
        L($"  preserves owns {args} saved x p m");
        L("  returns result:unit");
        L($"  ensures pure ({EnumerableAdapter.Fact(e, "(reveal m).O.items", "(reveal m).O.scalar")})");
        L("{");
        L($"  unfold (owns {args} saved x p m);");
        if (d.View is not null) L("  with v. _;");
        L($"  fold (owns {args} saved x p m);");
        L("}");
        L($"let api {binders} (saved:erased ({sourceModel})) =");
        L($"  API.make #{Types.Atom(e.Element)} #{Types.Atom(e.Capability!.ScalarType)} " +
            $"#(fun (m:{model}) -> {fact}) #({sourceType}) #(owns {args} saved) " +
            $"(O.make (length {args} saved) (scalar {args} saved)) (iterator_slots {args} saved) (facts {args} saved)");
        L($"let descriptor {binders} (saved:erased ({sourceModel})) (x:{sourceType})");
        L($"  : w:C.descriptor ({model}) ({EnumerableAdapter.Api(e)}) {{ C.supports w }} =");
        L($"  C.make #({model}) #({EnumerableAdapter.Api(e)}) ({sourceType}) (owns {args} saved) x (Some (api {args} saved))");
        return new EmittedModule(d.Module, text.ToString()) {
            Origin = [new Provenance("*", d.Items.Loc)], Origins = [new LineOrigin(1, d.Items.Loc)]
        };
    }
}
