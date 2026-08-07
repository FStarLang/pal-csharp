using PalLang;

namespace PalCSharp.Tests;

/// <summary>
/// Iterative walks over a chain. Compare <c>test/generic_list</c>'s <c>Chains</c>, where
/// every operation is recursive — not because a list is naturally recursive, but because
/// §10's derived invariant left no other option (§10.7). These are the same functions
/// written the way a C# programmer writes them, with a <c>while</c> loop and a cursor.
///
/// <para>Every proof step is an ordinary C# call to a <c>[Lemma]</c> declared in
/// <c>Cell.cs</c>. There is no raw Pulse in this file, no <c>Pal.GhostStmt</c>, and nothing
/// that names a Pulse existential — which is the claim a cursor has to make good on, because
/// the whole difficulty of an iterative walk is that the ownership it holds changes on every
/// iteration, and if the *user* cannot say how, the loop cannot be specified at all.</para>
///
/// <para>The invariant is the same three lines in every walk below, and it is worth reading
/// once: the prefix already walked, the suffix still to walk, and the arithmetic that says
/// where the split is. The two halves are <c>Take</c> and <c>Drop</c> of the counter, so
/// they are functions of a mutable local and R5.8 quantifies them for free.</para>
/// </summary>
public static class Walks
{
    /// <summary>
    /// Push a value onto the front of a chain — the one operation here that builds rather
    /// than walks, and the reason the other two have anything to walk.
    /// </summary>
    [Requires("Chain.Whole(head, xs)")]
    [Ensures("Chain.Whole(Result, SpecList.Cons(v, xs))")]
    public static Cell<T>? Push<T>(Cell<T>? head, T v, Ghost<SpecList<T>> xs = default)
    {
        Cell<T> node = new Cell<T> { value = v, next = head };
        ChainProof.Push(node, v, head, xs);
        return node;
    }

    /// <summary>
    /// The length of a chain, by walking it. The loop's exit condition is the cursor
    /// reaching <c>null</c>, and <see cref="ChainProof.AtEnd"/> is what turns that pointer
    /// test into the arithmetic fact <c>i == xs.Length</c> the postcondition needs.
    /// </summary>
    [Requires("Chain.Whole(head, xs)")]
    [Requires("xs.Length < 2147483647")]
    [Ensures("Chain.Whole(head, xs)")]
    [Ensures("Result == xs.Length")]
    public static int Count<T>(Cell<T>? head, Ghost<SpecList<T>> xs = default)
    {
        ChainProof.Start(head, xs);
        Cell<T>? cur = head;
        int i = 0;
        while (cur != null)
        {
            Pal.Invariant(Chain.Seg(head, cur, SpecList.Take(xs.Value, i)));
            Pal.Invariant(Chain.Whole(cur, SpecList.Drop(xs.Value, i)));
            Pal.Invariant(0 <= i && i <= xs.Value.Length);
            Pal.Invariant(xs.Value.Length < 2147483647);
            Pal.Decreases(xs.Value.Length - i);

            ChainProof.AtEnd(cur, i, xs);
            ChainProof.Open(cur, cur!, SpecList.Drop(xs.Value, i));
            T v = cur.value;
            Cell<T>? nx = cur.next;
            ChainProof.Advance(head, cur, cur!, v, nx, i, xs);
            cur = nx;
            i = i + 1;
        }
        ChainProof.Finish(head, cur, i, xs);
        return i;
    }

    /// <summary>
    /// Element <paramref name="n"/>, by walking to it.
    ///
    /// <para>The loop is the one in <see cref="Count"/> and only the condition differs, which
    /// is the payoff of having stated the invariant in terms of the counter. The interesting
    /// line is the last <see cref="ChainProof.Close"/>: this walk stops in the *middle* of the
    /// chain, and it costs one lemma call rather than a special case, because the two halves
    /// compose at any split point.</para>
    ///
    /// <para>It is also what pins the output half of <see cref="ChainProof.Advance"/> — that
    /// the value read out of a cell is element <c>i</c> of the list the caller passed in —
    /// which is what makes a cursor useful for anything beyond counting.</para>
    /// </summary>
    [Requires("Chain.Whole(head, xs)")]
    [Requires("0 <= n && n < xs.Length && xs.Length < 2147483647")]
    [Ensures("Chain.Whole(head, xs)")]
    [Ensures("Pal.Same(Result, xs[n])")]
    public static T ElementAt<T>(Cell<T>? head, int n, Ghost<SpecList<T>> xs = default)
    {
        ChainProof.Start(head, xs);
        Cell<T>? cur = head;
        int i = 0;
        while (i < n)
        {
            Pal.Invariant(Chain.Seg(head, cur, SpecList.Take(xs.Value, i)));
            Pal.Invariant(Chain.Whole(cur, SpecList.Drop(xs.Value, i)));
            Pal.Invariant(0 <= i && i <= n);
            Pal.Invariant(n < xs.Value.Length && xs.Value.Length < 2147483647);
            Pal.Decreases(n - i);

            ChainProof.AtEnd(cur, i, xs);
            ChainProof.Open(cur, cur!, SpecList.Drop(xs.Value, i));
            T skipped = cur!.value;
            Cell<T>? nx = cur!.next;
            ChainProof.Advance(head, cur, cur!, skipped, nx, i, xs);
            cur = nx;
            i = i + 1;
        }

        // Out of the loop with `i == n`, so the cell under the cursor is the one wanted. The
        // last three lines are the loop body again, with `Close` in place of the assignments.
        ChainProof.AtEnd(cur, i, xs);
        ChainProof.Open(cur, cur!, SpecList.Drop(xs.Value, i));
        T found = cur!.value;
        Cell<T>? rest = cur!.next;
        ChainProof.Advance(head, cur, cur!, found, rest, i, xs);
        ChainProof.Close(head, rest, i + 1, xs);
        return found;
    }
}
