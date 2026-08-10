using PalLang;

namespace PalCSharp.Tests;

/// <summary>
/// R5.3, and the one thing its expansion must not lose.
///
/// <para><c>x op= e</c> and <c>x++</c> are notations for <c>x = x op e</c>, so the
/// expansion names the L-value twice — three times for the expression form, which also
/// snapshots it. C# names it once and evaluates it once (ECMA-334 §12.18.3, §12.21). For
/// an L-value like <c>a[Bump(ref cursor)]</c> the difference is not a subtlety: the
/// expansion calls <c>Bump</c> twice, so it advances the cursor by two and increments an
/// element the C# never touches. A proof about that expansion is a theorem about a
/// different program, and every postcondition it discharges is available to be
/// false.</para>
///
/// <para>So the effectful part of an L-value is evaluated once, into an immutable local,
/// and each copy of the L-value names that local — the same discipline R5.14 already
/// applies to a <c>switch</c> scrutinee. This file is written so that a translation which
/// duplicated the L-value would fail: every contract here counts the calls.</para>
/// </summary>
public static class Stepping
{
    /// <summary>
    /// A cursor that advances by exactly one and reports where it was. Its contract is
    /// what makes the number of evaluations observable in a specification.
    /// </summary>
    [Requires("0 <= cursor && cursor < 1000")]
    [Ensures("cursor == Old(cursor) + 1")]
    [Ensures("Result == Old(cursor)")]
    public static int Bump(ref int cursor)
    {
        int r = cursor;
        cursor = cursor + 1;
        return r;
    }

    /// <summary>
    /// <c>a[Bump(ref cursor)]++</c>. One call, so the cursor advances by one; and the
    /// element that is incremented is the one the single call named.
    /// </summary>
    [Requires("0 <= cursor && cursor < a.Length && a.Length < 1000")]
    [Requires("a[cursor] == 0")]
    [Ensures("cursor == Old(cursor) + 1")]
    [Ensures("a.Length == Old(a.Length)")]
    public static void PokeOnce(int[] a, ref int cursor)
    {
        a[Bump(ref cursor)]++;
    }

    /// <summary>
    /// The same for a compound assignment, whose expansion has the same shape.
    /// </summary>
    [Requires("0 <= cursor && cursor < a.Length && a.Length < 1000")]
    [Requires("a[cursor] == 0")]
    [Ensures("cursor == Old(cursor) + 1")]
    [Ensures("a.Length == Old(a.Length)")]
    public static void AddOnce(int[] a, ref int cursor)
    {
        a[Bump(ref cursor)] += 5;
    }

    /// <summary>
    /// The expression form, which mentions the L-value a third time to snapshot it. The
    /// result is the element's *old* value, so a translation that read it from a second
    /// evaluation of the index would be reading a different element.
    /// </summary>
    [Requires("0 <= cursor && cursor < a.Length && a.Length < 1000")]
    [Requires("a[cursor] == 0")]
    [Ensures("cursor == Old(cursor) + 1")]
    [Ensures("Result == 0")]
    public static int PokeExpr(int[] a, ref int cursor)
    {
        return a[Bump(ref cursor)]++;
    }

    /// <summary>
    /// An index that steps a local rather than calling anything: <c>a[i++] += 1</c>
    /// advances <c>i</c> once, not twice. The lowering of <c>i++</c> is itself a
    /// statement-expression with a prelude, so duplicating the L-value would duplicate
    /// that prelude.
    /// </summary>
    [Requires("a.Length >= 2")]
    [Requires("a[0] == 0")]
    [Ensures("Result == 1")]
    public static int StepIndexOnce(int[] a)
    {
        int i = 0;
        a[i++] += 1;
        return i;
    }
}
