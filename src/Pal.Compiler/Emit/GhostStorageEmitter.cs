using System.Text;
using System.Collections.Immutable;
using Pal.Compiler.Ir;

namespace Pal.Compiler.Emit;

internal static class GhostStorageEmitter
{
    public static string CheckName(string owner, IrFieldDecl field) =>
        $"ghost_storage_{owner}_{field.Name}";

    public static void Checks(StringBuilder sb, IrClass c)
        => Checks(sb, c.Name, c.Fields, c.TypeParameters);

    public static void Checks(StringBuilder sb, string name, ImmutableArray<IrFieldDecl> fields,
        ImmutableArray<string> typeParameters)
    {
        foreach (var field in fields.Where(f => f.IsGhost))
        {
            // Check a function's DOMAIN, not a value: F* must not insert `hide`
            // and thereby accept an informative type. This is checked even if
            // no constructor or update of the field is ever translated.
            sb.AppendLine($"let {CheckName(name, field)}{new TypeBinders(typeParameters).Implicit} () : Lemma True =");
            sb.AppendLine($"  Pulse.Lib.CSharp.Ownership.require_erased (id #{Types.Atom(field.Type)})");
            sb.AppendLine();
        }
    }
}
