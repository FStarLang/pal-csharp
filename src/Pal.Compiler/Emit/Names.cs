using Pal.Compiler.Ir;

namespace Pal.Compiler.Emit;

/// <summary>
/// What a Pulse term denotes, so that the emitter can insert the one coercion the
/// C#-to-Pulse gap requires — <c>Int32.v</c> between a machine integer and the
/// mathematical integer a specification talks about — and no others.
/// </summary>
public enum TermKind
{
    /// <summary>A mathematical <c>int</c> / <c>nat</c>.</summary>
    Math,
    /// <summary>A machine integer such as <c>Int32.t</c>.</summary>
    Machine,
    Bool,
    Prop,
    /// <summary>A <c>Seq.seq</c>.</summary>
    Seq,
    /// <summary>A live Pulse <c>array</c>.</summary>
    Array,
    Other,
}

/// <summary>A Pulse term together with what it denotes.</summary>
public readonly record struct Term(string Text, TermKind Kind, IrType? Type = null)
{
    public override string ToString() => Text;
}

/// <summary>Naming conventions (doc/translation.md R2.1).</summary>
public static class Names
{
    public static string Local(string name) => "var_" + name;
    public static string Argument(string name) => "arg_" + name;
    public static string Function(string name) => "func_" + name;
    public static string SpecFunction(string name) => "spec_" + name;
    public static string Lemma(string name) => "lemma_" + name;
    public static string FunctionModule(string name) => "Func_" + name;
    public static string SpecModule(string name) => "Let_" + name;
    public const string Result = "var_result";
}

/// <summary>The Pulse rendering of a C# type (doc/translation.md §3).</summary>
public static class Types
{
    public static string Machine(PrimKind kind) => kind switch
    {
        PrimKind.Bool => "bool",
        PrimKind.SByte => "I8.t",
        PrimKind.Byte => "U8.t",
        PrimKind.Short => "I16.t",
        PrimKind.UShort => "U16.t",
        PrimKind.Int => "I32.t",
        PrimKind.UInt => "U32.t",
        PrimKind.Long => "I64.t",
        PrimKind.ULong => "U64.t",
        PrimKind.Char => "U16.t",
        PrimKind.Void => "unit",
        PrimKind.SpecInt => "int",
        PrimKind.SpecNat => "nat",
        PrimKind.SlProp => "slprop",
        _ => "unit",
    };

    /// <summary>The F* module qualifying a machine integer's operations.</summary>
    public static string Module(PrimKind kind) => kind switch
    {
        PrimKind.SByte => "I8",
        PrimKind.Byte => "U8",
        PrimKind.Short => "I16",
        PrimKind.UShort => "U16",
        PrimKind.Int => "I32",
        PrimKind.UInt => "U32",
        PrimKind.Long => "I64",
        PrimKind.ULong => "U64",
        PrimKind.Char => "U16",
        _ => "I32",
    };

    /// <summary>Bit width, used by the R5.9 case-2 measure.</summary>
    public static int Width(PrimKind kind) => kind switch
    {
        PrimKind.SByte or PrimKind.Byte => 8,
        PrimKind.Short or PrimKind.UShort or PrimKind.Char => 16,
        PrimKind.Long or PrimKind.ULong => 64,
        _ => 32,
    };

    public static bool IsSigned(PrimKind kind) =>
        kind is PrimKind.SByte or PrimKind.Short or PrimKind.Int or PrimKind.Long;

    public static string Render(IrType type) => type switch
    {
        IrPrim p => Machine(p.Kind),
        IrArrayType a => $"array {Render(a.Element)}",
        IrSeqType s => $"Seq.seq {Render(s.Element)}",
        IrGhostType g => Render(g.Inner),
        IrNamedType n => "struct_" + n.Name,
        IrPulseType p => p.PulseText,
        _ => "unit",
    };

    /// <summary>The literal syntax for a value of a machine-integer type.</summary>
    public static string Literal(object? value, IrType? type)
    {
        switch (value)
        {
            case null: return "()";
            case bool b: return b ? "true" : "false";
        }

        var kind = (type as IrPrim)?.Kind ?? PrimKind.Int;
        var text = Convert.ToString(value, System.Globalization.CultureInfo.InvariantCulture) ?? "0";
        var suffix = kind switch
        {
            PrimKind.Int => "l",
            PrimKind.Long => "L",
            PrimKind.UInt => "ul",
            PrimKind.ULong => "uL",
            PrimKind.Short => "s",
            PrimKind.UShort => "us",
            PrimKind.SByte => "y",
            PrimKind.Byte => "uy",
            PrimKind.SpecInt or PrimKind.SpecNat => "",
            _ => "l",
        };
        return text.StartsWith('-') ? $"({text}{suffix})" : text + suffix;
    }
}
