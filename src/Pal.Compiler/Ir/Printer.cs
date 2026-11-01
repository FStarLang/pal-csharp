using System.Text;

namespace Pal.Compiler.Ir;

/// <summary>
/// A readable dump of the IR, for <c>palcs --print-ir</c>. This is a debugging aid: it
/// shows what the front end actually built, which is usually where a surprising
/// translation comes from.
/// </summary>
public static class Printer
{
    public static string Print(IrProgram program)
    {
        var sb = new StringBuilder();
        foreach (var decl in program.Declarations) Decl(sb, decl);
        return sb.ToString();
    }

    private static void Decl(StringBuilder sb, IrDecl decl)
    {
        switch (decl)
        {
            case IrMethod m:
                sb.Append(m.IsLemma ? "lemma " : "method ").Append(m.Name).Append('(')
                  .Append(string.Join(", ", m.Parameters.Select(p =>
                      $"{(p.Mode == ParamMode.Value ? "" : p.Mode.ToString().ToLowerInvariant() + " ")}" +
                      $"{(p.IsGhost ? "ghost " : "")}{p.Type} {p.Name}")))
                  .Append(") : ").Append(m.ReturnType).AppendLine();
                foreach (var r in m.Requires) sb.Append("  requires ").AppendLine(r.ToString());
                foreach (var e in m.Ensures) sb.Append("  ensures  ").AppendLine(e.ToString());
                if (m.Body is not null) Stmt(sb, m.Body, 1);
                if (m.PulseBody is { } raw) sb.Append("  pulse { ").Append(raw).AppendLine(" }");
                sb.AppendLine();
                return;

            case IrSpecFunction s:
                sb.Append("spec ").Append(s.Name).Append('(')
                  .Append(string.Join(", ", s.Parameters.Select(p => $"{p.Type} {p.Name}")))
                  .Append(") : ").Append(s.ReturnType).AppendLine();
                foreach (var r in s.Requires) sb.Append("  requires ").AppendLine(r.ToString());
                sb.Append("  = ").AppendLine(s.Body.ToString());
                sb.AppendLine();
                return;

            case IrIncludePulse i:
                sb.Append("include_pulse ").AppendLine(i.Module).AppendLine();
                return;

            default:
                sb.AppendLine(decl.ToString());
                return;
        }
    }

    private static void Stmt(StringBuilder sb, IrStmt stmt, int depth)
    {
        var pad = new string(' ', depth * 2);
        switch (stmt)
        {
            case IrBlock b:
                sb.Append(pad).AppendLine("{");
                foreach (var s in b.Statements) Stmt(sb, s, depth + 1);
                sb.Append(pad).AppendLine("}");
                return;

            case IrLocalDecl d:
                sb.Append(pad).Append(d.Type).Append(' ').Append(d.Name)
                  .Append(d.Init is null ? "" : " = " + d.Init).AppendLine(";");
                return;

            case IrAssign a:
                sb.Append(pad).Append(a.Target).Append(" = ").Append(a.Value).AppendLine(";");
                return;

            case IrIf i:
                sb.Append(pad).Append("if (").Append(i.Cond).AppendLine(")");
                Stmt(sb, i.Then, depth + 1);
                if (i.Else is not null) { sb.Append(pad).AppendLine("else"); Stmt(sb, i.Else, depth + 1); }
                return;

            case IrWhile w:
                sb.Append(pad).Append("while (").Append(w.Cond).AppendLine(")");
                foreach (var inv in w.Invariants) sb.Append(pad).Append("  invariant ").AppendLine(inv.ToString());
                if (w.Decreases is not null) sb.Append(pad).Append("  decreases ").AppendLine(w.Decreases.ToString());
                sb.Append(pad).Append("  live [").Append(string.Join(", ", w.Live))
                  .Append("] unassigned [").Append(string.Join(", ", w.Unassigned)).AppendLine("]");
                Stmt(sb, w.Body, depth + 1);
                return;

            case IrGhostStmt g:
                sb.Append(pad).Append("ghost ").Append(g.Kind).Append(' ')
                  .AppendLine(g.Text ?? g.Prop?.ToString() ?? "");
                return;

            case IrReturn r:
                sb.Append(pad).Append("return ").Append(r.Value?.ToString() ?? "").AppendLine(";");
                return;

            case IrThrow t:
                sb.Append(pad).Append("throw ").Append(t.Value?.ToString() ?? "").AppendLine(";");
                return;

            case IrTry t:
                sb.Append(pad).AppendLine("try");
                sb.Append(pad).Append("  live [").Append(string.Join(", ", t.Live))
                  .Append("] unassigned [").Append(string.Join(", ", t.Unassigned)).AppendLine("]");
                foreach (var inv in t.Invariants) sb.Append(pad).Append("  invariant ").AppendLine(inv.ToString());
                Stmt(sb, t.Body, depth + 1);
                foreach (var c in t.Catches)
                {
                    sb.Append(pad).Append("catch (").Append(c.Type).Append(' ').Append(c.Var ?? "_").Append(')');
                    if (c.When is not null) sb.Append(" when (").Append(c.When).Append(')');
                    sb.AppendLine();
                    Stmt(sb, c.Body, depth + 1);
                }
                return;

            default:
                sb.Append(pad).AppendLine(stmt.ToString());
                return;
        }
    }
}
