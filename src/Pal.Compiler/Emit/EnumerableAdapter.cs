using Pal.Compiler.Ir;

namespace Pal.Compiler.Emit;

internal static class EnumerableAdapter
{
    public const string Module = "Pulse.Lib.CSharp.Enumerable.Cast";
    public const string Source = "Pulse.Lib.CSharp.Enumerable.Source";
    public const string Capability = "Pulse.Lib.CSharp.Enumerable.Capability";
    public const string Observation = "Pulse.Lib.CSharp.Enumerable.Observation";
    public const string Iterator = "Pulse.Lib.CSharp.Enumerable.Iterator";
    public const string IteratorModel = "Pulse.Lib.CSharp.Capability.Iterator";
    public static string Operations(IrEnumerableType e) =>
        e.Capability?.Iteration is null ? Observation : Observation + ".Iterable";
    public static string Logical(IrEnumerableType e) =>
        $"{Observation}.model {Types.Atom(e.Element)} {Types.Atom(e.Capability!.ScalarType)}";
    public static string Api(IrEnumerableType e) =>
        $"{Operations(e)}.slots {Types.Atom(e.Element)} {Types.Atom(e.Capability!.ScalarType)}" +
        (e.Capability.Iteration is null ? "" :
            $" (fun m -> {Fact(e, $"({Observation}.contents m)", $"({Observation}.scalar m)")})");
    public static string Fact(IrEnumerableType e, string items, string scalar) =>
        $"NominalFacts_{e.CastTarget!.Name}.fact " +
        string.Join(" ", e.CastTarget.TypeArguments.Select(Types.Atom)) + $" {items} {scalar}";
    public static string AbstractFact(IrEnumerableType e, string name) =>
        $"(fun m -> {Fact(e, $"(enum_contents_{name} m)", $"(enum_scalar_{name} m)")})";
    public static string Misses(string name) => "misses_" + name;
    public static string ModelType(IrClassType c) =>
        Types.Applied($"{Names.ClassModule(c.Name)}.{Names.ClassModel(c.Name)}", c.TypeArguments);
    public static string RevealModel(IrClassType c, string name) =>
        $"(FStar.Ghost.reveal #({ModelType(c)}) {name})";
    public static string Owns(IrClassType c) =>
        $"(fun (x: {Types.Render(c)}) p (m: {ModelType(c)}) -> {Names.ClassModule(c.Name)}.{Names.ClassInv(c.Name)} x #p m)";
    public static string Projection(IrClassType c, string? property) =>
        $"(fun (m: {ModelType(c)}) -> " +
        (property is null ? "m)" :
            $"{Names.ClassModule(c.Name)}.{Names.Observation(c.Name, property)} " +
            string.Concat(c.TypeArguments.Select(t => $"#{Types.Atom(t)} ")) + "m)");
    public static string Arguments(IrEnumerableType e) =>
        $"{Owns(e.CastTarget!)} {Projection(e.CastTarget!, e.CastProjection)}";
    public static string Resource(IrEnumerableType e, string name) =>
        $"({Module}.resource {Arguments(e)} {Misses(name)})";
    public static string PtsTo(IrEnumerableType e, string name, string binder, string p, string items) =>
        e.Capability is not null
            ? $"{Capability}.pts_to enum_contents_{name} {binder} descriptor_{name} {p} {items}"
            : $"{Source}.pts_to {Resource(e, name)} {Module}.contents {binder} {p} {items}";
}
