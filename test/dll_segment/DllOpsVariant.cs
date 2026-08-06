using PalLang;

namespace PalCSharp.Tests;

/// <summary>
/// The §7.2 variant: the same two operations written independently — the null test is
/// inverted, the locals are named and ordered differently, and <c>Prepend</c> returns early
/// from the impossible branch rather than using an <c>else</c>. It calls the same published
/// lemmas, because that is the whole point: the proof steps belong to the *predicate*, not
/// to a particular rendering of the program. It must verify with no translator change.
/// </summary>
public static class DllOpsVariant
{
    [Requires("Dll.Seg(cursor, back, null, final, items)")]
    [Requires("items.Length < 2147483647")]
    [Ensures("Dll.Seg(cursor, back, null, final, items)")]
    [Ensures("Result == items.Length")]
    [Decreases("items")]
    public static int Count(DNode? cursor, DNode? back, DNode? final,
                            Ghost<SpecList<SpecInt>> items = default)
    {
        DllProof.Cases(cursor, back, final, items);
        if (cursor != null)
        {
            DllProof.Open(cursor, cursor, back, null, final, items);
            DNode? onward = cursor.next;
            int seen = Count(onward, cursor, final);
            DllProof.Close(cursor, cursor, back, null, final, items);
            return 1 + seen;
        }
        return 0;
    }

    [Requires("Dll.Whole(first, stop, items)")]
    [Requires("items.Length > 0")]
    [Ensures("Dll.Whole(Result, stop, SpecList.Cons(x, items))")]
    public static DNode? Prepend(DNode? first, DNode? stop, int x,
                                 Ghost<SpecList<SpecInt>> items = default)
    {
        DllProof.Cases(first, null, stop, items);
        if (first == null)
        {
            Pal.GhostStmt("unreachable ()");
            return null;
        }

        DNode fresh = new DNode { value = x, prev = null, next = first };
        DllProof.Open(first, first, null, null, stop, items);
        first.prev = fresh;
        DllProof.Close(first, first, fresh, null, stop, items);
        DllProof.Cons(fresh, x, null, first, null, stop, items);
        return fresh;
    }
}
