using PalLang;

namespace PalCSharp.Tests;

/// <summary>
/// Operations over the user's predicate. Every proof step here is an ordinary C# call to a
/// <c>[Lemma]</c> declared in <c>Dll.cs</c> — there is no raw Pulse in this file at all.
/// The translator places what the user named and derives nothing.
/// </summary>
public static class DllOps
{
    /// <summary>
    /// The length of a segment whose right boundary is the end of the list. The recursion
    /// walks the segment and puts it back, which is what <c>Close</c> is for.
    /// </summary>
    [Requires("Dll.Seg(from, prev, null, last, xs)")]
    [Requires("xs.Length < 2147483647")]
    [Ensures("Dll.Seg(from, prev, null, last, xs)")]
    [Ensures("Result == xs.Length")]
    [Decreases("xs")]
    public static int Length(DNode? from, DNode? prev, DNode? last,
                             Ghost<SpecList<SpecInt>> xs = default)
    {
        // The `if` below is a case split on the *list*, and only the user's lemma says so:
        // for a general segment emptiness is `from == to`, not `from == null`.
        DllProof.Cases(from, prev, last, xs);
        if (from == null)
        {
            return 0;
        }
        // `from!` is C#'s null-forgiving operator, and it is what the C# compiler already
        // demands in order to pass a `DNode?` where a `DNode` is declared. R10.2c reads the
        // same declaration and projects, so the opened predicate lands on exactly the node
        // the field reads below go through.
        DllProof.Open(from, from!, prev, null, last, xs);
        int rest = Length(from.next, from, last);
        DllProof.Close(from, from!, prev, null, last, xs);
        return rest + 1;
    }

    /// <summary>
    /// Pushing onto the front of a non-empty list. This is the operation a doubly linked
    /// list exists for and the one §10 could never reach: it *writes the old head's back
    /// pointer*, and the write is discharged because the predicate only ever constrained
    /// that field rather than owning it. Re-closing the segment simply reports what the
    /// field now holds — which is why <c>Close</c> is passed <c>node</c> as the new left
    /// boundary and needs nothing else.
    /// </summary>
    [Requires("Dll.Whole(head, tail, xs)")]
    [Requires("!xs.IsEmpty")]
    [Ensures("Dll.Whole(Result, tail, SpecList.Cons(v, xs))")]
    public static DNode? PushFront(DNode? head, DNode? tail, int v,
                                  Ghost<SpecList<SpecInt>> xs = default)
    {
        DNode node = new DNode { value = v, prev = null, next = head };
        DllProof.Cases(head, null, tail, xs);
        if (head == null)
        {
            // `Cases` and the non-empty precondition contradict, so this branch is dead --
            // and it is the user's lemma that says so.
            Pal.GhostStmt("unreachable ()");
            return null;
        }
        else
        {
            DllProof.Open(head, head!, null, null, tail, xs);
            head.prev = node;
            DllProof.Close(head, head!, node, null, tail, xs);
            DllProof.Cons(node, v, null, head, null, tail, xs);
            return node;
        }
    }
}
