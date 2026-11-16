using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;

namespace Pal.Compiler.Frontend;

/// <summary>
/// R30.1, R30.2. Whether a local that stands for a field's array — an array local copied
/// from the field (R24.19), or a <c>ref</c> local into it (R24.8) — is <em>current</em>
/// wherever it is used: bound since the field last changed. The field may change by an
/// assignment to it, or by a call of another instance method of the class; a rebinding
/// (<c>a = _f;</c>, <c>r = ref e;</c>, as a statement) makes the local current again. A
/// local that is current everywhere it is read names exactly what the field names there,
/// so every use of it can be the field's.
///
/// The walk follows C#'s evaluation order and is conservative: a change inside an
/// expression's branch is taken to have happened, a rebinding counts only as a statement,
/// and anything it does not understand (<c>goto</c>, a lambda that names the local) fails.
/// </summary>
internal sealed class AliasFlow(
    SemanticModel model,
    WellKnown known,
    ILocalSymbol local,
    ISet<ISymbol> fields,
    Func<ExpressionStatementSyntax, bool> isRebind)
{
    private bool _ok = true;

    /// <summary>Where the check failed: a use that may be stale, or a construct it cannot follow.</summary>
    public SyntaxNode? Failure { get; private set; }

    private bool Fail(SyntaxNode at)
    {
        if (_ok) Failure = at;
        _ok = false;
        return false;
    }
    private readonly Stack<(List<bool> Breaks, List<bool> Continues)> _loops = new();

    /// <summary>
    /// Whether the local is current at each of its uses in the statements following its
    /// declaration in <paramref name="scope"/>, starting <paramref name="current"/>.
    /// </summary>
    public bool Check(SyntaxNode scope, SyntaxNode declaration, bool current)
    {
        var state = current;
        var started = false;
        foreach (var st in scope.ChildNodes().OfType<StatementSyntax>())
        {
            if (!started)
            {
                started = st == declaration || st.Contains(declaration);
                continue;
            }
            state = Statement(st, state);
            if (!_ok) return false;
        }
        return _ok && started;
    }

    private const bool Unreached = true;

    private bool Statement(StatementSyntax st, bool s)
    {
        if (!_ok) return s;
        switch (st)
        {
            case BlockSyntax b:
                foreach (var x in b.Statements) s = Statement(x, s);
                return s;
            case ExpressionStatementSyntax e when isRebind(e):
                Expr(((AssignmentExpressionSyntax)e.Expression).Right is RefExpressionSyntax r
                    ? r.Expression : ((AssignmentExpressionSyntax)e.Expression).Right, s);
                return true;
            case ExpressionStatementSyntax e:
                return Expr(e.Expression, s);
            case LocalDeclarationStatementSyntax d:
                foreach (var v in d.Declaration.Variables)
                    if (v.Initializer is { } init) s = Expr(init.Value, s);
                return s;
            case IfStatementSyntax i:
            {
                s = Expr(i.Condition, s);
                var t = Statement(i.Statement, s);
                var f = i.Else is null ? s : Statement(i.Else.Statement, s);
                return t && f;
            }
            case WhileStatementSyntax w:
                return Loop(s, h => Expr(w.Condition, h), h => Statement(w.Statement, h), conditionFirst: true);
            case DoStatementSyntax d:
                return Loop(s, h => Expr(d.Condition, h), h => Statement(d.Statement, h), conditionFirst: false);
            case ForStatementSyntax f:
            {
                if (f.Declaration is { } decl)
                    foreach (var v in decl.Variables)
                        if (v.Initializer is { } init) s = Expr(init.Value, s);
                foreach (var init in f.Initializers) s = Expr(init, s);
                return Loop(s, h => f.Condition is null ? h : Expr(f.Condition, h),
                    h =>
                    {
                        h = Statement(f.Statement, h);
                        foreach (var inc in f.Incrementors) h = Expr(inc, h);
                        return h;
                    }, conditionFirst: true);
            }
            case ForEachStatementSyntax fe:
                s = Expr(fe.Expression, s);
                return Loop(s, h => h, h => Statement(fe.Statement, h), conditionFirst: true);
            case ReturnStatementSyntax ret:
                if (ret.Expression is not null) Expr(ret.Expression, s);
                return Unreached;
            case ThrowStatementSyntax t:
                if (t.Expression is not null) Expr(t.Expression, s);
                return Unreached;
            case BreakStatementSyntax:
                if (_loops.Count == 0) { Fail(st); return s; }
                _loops.Peek().Breaks.Add(s);
                return Unreached;
            case ContinueStatementSyntax:
                if (_loops.Count == 0) { Fail(st); return s; }
                _loops.Peek().Continues.Add(s);
                return Unreached;
            case EmptyStatementSyntax:
                return s;
            case CheckedStatementSyntax c:
                return Statement(c.Block, s);
            default:
                // `goto`, `switch`, `try`, `using`, labels...: current only if the local is
                // not involved at all.
                if (Mentions(st) || Changes(st)) Fail(st);
                return s;
        }
    }

    private bool Loop(bool entry, Func<bool, bool> condition, Func<bool, bool> body, bool conditionFirst)
    {
        var head = entry;
        for (var round = 0; round < 3; round++)
        {
            _loops.Push(([], []));
            var h = conditionFirst ? condition(head) : head;
            var end = body(h);
            var frame = _loops.Pop();
            if (!conditionFirst) end = condition(end && frame.Continues.All(c => c));
            var again = head && end && frame.Continues.All(c => c);
            var exit = (conditionFirst ? h : end) && frame.Breaks.All(b => b);
            if (again == head) return exit;
            head = again;
        }
        return Fail(Failure ?? local.DeclaringSyntaxReferences[0].GetSyntax());
    }

    private bool Expr(ExpressionSyntax e, bool s)
    {
        if (!_ok) return s;
        foreach (var n in Ordered(e))
        {
            if (n is AnonymousFunctionExpressionSyntax lambda)
            {
                if (Mentions(lambda)) Fail(lambda);
                continue;
            }
            if (Uses(n) && !s) { Fail(n); return s; }
            if (Invalidates(n)) s = false;
        }
        return s;
    }

    /// <summary>The nodes of <paramref name="e"/>, each after the ones evaluated before it.</summary>
    private static IEnumerable<SyntaxNode> Ordered(SyntaxNode e)
    {
        if (e is AnonymousFunctionExpressionSyntax) { yield return e; yield break; }
        if (e is AssignmentExpressionSyntax a)
        {
            // The target's receiver and index first, then the value, then the store.
            foreach (var n in Ordered(a.Left)) if (n != a.Left) yield return n;
            foreach (var n in Ordered(a.Right)) yield return n;
            yield return a.Left;
            yield return a;
            yield break;
        }
        foreach (var c in e.ChildNodes())
            foreach (var n in Ordered(c))
                yield return n;
        yield return e;
    }

    private bool Uses(SyntaxNode n) =>
        n is IdentifierNameSyntax &&
        SymbolEqualityComparer.Default.Equals(model.GetSymbolInfo(n).Symbol, local);

    private bool Mentions(SyntaxNode n) => n.DescendantNodesAndSelf().Any(Uses);

    private bool Changes(SyntaxNode n) => n.DescendantNodesAndSelf().Any(Invalidates);

    private bool Invalidates(SyntaxNode n)
    {
        ExpressionSyntax? target = n switch
        {
            AssignmentExpressionSyntax a => a.Left,
            PrefixUnaryExpressionSyntax u when u.IsKind(SyntaxKind.PreIncrementExpression) ||
                                               u.IsKind(SyntaxKind.PreDecrementExpression) => u.Operand,
            PostfixUnaryExpressionSyntax u when u.IsKind(SyntaxKind.PostIncrementExpression) ||
                                                u.IsKind(SyntaxKind.PostDecrementExpression) => u.Operand,
            ArgumentSyntax { RefKindKeyword.RawKind: not (int)SyntaxKind.None } arg => arg.Expression,
            _ => null,
        };
        var self = local.ContainingSymbol.ContainingType;
        if (target is not null && model.GetSymbolInfo(target).Symbol is { } written &&
            (written is IFieldSymbol f && fields.Contains(f) ||
             written is IPropertySymbol { IsStatic: false } p &&
             SymbolEqualityComparer.Default.Equals(p.ContainingType?.OriginalDefinition, self?.OriginalDefinition)))
            return true;
        if (n is not InvocationExpressionSyntax inv ||
            model.GetSymbolInfo(inv).Symbol is not IMethodSymbol m ||
            Declarations.Has(m, known.LemmaAttribute))
            return false;
        bool Own(ITypeSymbol? t) =>
            SymbolEqualityComparer.Default.Equals(t?.OriginalDefinition, self?.OriginalDefinition);
        // A call of another of the class's methods on this object, or of anything this
        // object is handed to, may replace the field.
        return Own(m.ContainingType) && (!m.IsStatic && !ReadOnlyRef(m) || m.Parameters.Any(q => Own(q.Type))) ||
               inv.ArgumentList.Arguments.Any(a => a.Expression is ThisExpressionSyntax);
    }

    /// <summary>
    /// A <c>ref</c>-returning method that R24.9 inlines and that neither calls nor writes
    /// anything: binding a reference through it changes no field.
    /// </summary>
    private static bool ReadOnlyRef(IMethodSymbol m) =>
        m.ReturnsByRef && m.DeclaringSyntaxReferences is [var r] &&
        !r.GetSyntax().DescendantNodes().Any(n => n is InvocationExpressionSyntax or AssignmentExpressionSyntax ||
            n is PrefixUnaryExpressionSyntax or PostfixUnaryExpressionSyntax &&
            (n.IsKind(SyntaxKind.PreIncrementExpression) || n.IsKind(SyntaxKind.PreDecrementExpression) ||
             n.IsKind(SyntaxKind.PostIncrementExpression) || n.IsKind(SyntaxKind.PostDecrementExpression)));
}
