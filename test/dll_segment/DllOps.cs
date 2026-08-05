using PalLang;

namespace PalCSharp.Tests;

/// <summary>
/// Operations over the user's predicate. Every proof step here is a call to a lemma
/// declared in <c>Dll.cs</c>; the translator places what the user named and derives nothing.
/// </summary>
public static class DllOps
{
    /// <summary>
    /// The length of a segment whose right boundary is the end of the list. The recursion
    /// walks the segment and puts it back, which is what <c>intro_cons</c> is for.
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
        Pal.GhostStmt("DllSeg.dll_cases 1.0R $(from) $(prev) $(last) #$(xs)");
        if (from == null)
        {
            return 0;
        }
        Pal.GhostStmt("DllSeg.dll_seg_elim_cons 1.0R $(from) $(prev) None $(last) #$(xs)");
        Pal.GhostStmt(
            "with r tl. assert (DllSeg.dll_seg 1.0R r.Class_DNode.fld_next $(from) None $(last) tl)");
        int rest = Length(from.next, from, last);
        Pal.GhostStmt("DllSeg.dll_seg_intro_cons 1.0R (Some?.v $(from)) None $(last) #r #tl");
        Pal.GhostStmt(
            "rewrite (DllSeg.dll_seg 1.0R (Some (Some?.v $(from))) r.Class_DNode.fld_prev None " +
            "$(last) (FStar.Int32.v r.Class_DNode.fld_value :: tl)) " +
            "as (DllSeg.dll_seg 1.0R $(from) $(prev) None $(last) $(xs))");
        return rest + 1;
    }

    /// <summary>
    /// Pushing onto the front of a non-empty list. This is the operation a doubly linked
    /// list exists for and the one §10 could never reach: it *writes the old head's back
    /// pointer*, and the write is discharged because the predicate only ever constrained
    /// that field rather than owning it. Re-closing the segment simply reports what the
    /// field now holds.
    /// </summary>
    [Requires("Dll.Whole(head, tail, xs)")]
    [Requires("!xs.IsEmpty")]
    [Ensures("Dll.Whole(Result, tail, SpecList.Cons(v, xs))")]
    public static DNode? PushFront(DNode? head, DNode? tail, int v,
                                  Ghost<SpecList<SpecInt>> xs = default)
    {
        DNode node = new DNode { value = v, prev = null, next = head };
        Pal.GhostStmt("with nr. assert (Pulse.Lib.Box.pts_to $(node) nr)");
        Pal.GhostStmt("DllSeg.dll_cases 1.0R $(head) None $(tail) #$(xs)");
        if (head == null)
        {
            // `dll_cases` and the non-empty precondition contradict, so this branch is
            // dead -- and it is the user's lemma that says so.
            Pal.GhostStmt("unreachable ()");
            return null;
        }
        else
        {
            Pal.GhostStmt("DllSeg.dll_seg_elim_cons 1.0R $(head) None None $(tail) #$(xs)");
            Pal.GhostStmt(
                "with hr htl. assert (DllSeg.dll_seg 1.0R hr.Class_DNode.fld_next $(head) None " +
                "$(tail) htl)");
            head.prev = node;
            Pal.GhostStmt(
                "with hr'. assert (Pulse.Lib.Box.pts_to (Some?.v $(head)) hr')");
            Pal.GhostStmt(
                "rewrite (DllSeg.dll_seg 1.0R hr.Class_DNode.fld_next $(head) None $(tail) htl) " +
                "as (DllSeg.dll_seg 1.0R hr'.Class_DNode.fld_next (Some (Some?.v $(head))) None " +
                "$(tail) htl)");
            Pal.GhostStmt(
                "DllSeg.dll_seg_intro_cons 1.0R (Some?.v $(head)) None $(tail) #hr' #htl");
            Pal.GhostStmt(
                "rewrite (DllSeg.dll_seg 1.0R (Some (Some?.v $(head))) hr'.Class_DNode.fld_prev " +
                "None $(tail) (FStar.Int32.v hr'.Class_DNode.fld_value :: htl)) " +
                "as (DllSeg.dll_seg 1.0R nr.Class_DNode.fld_next (Some $(node)) None $(tail) $(xs))");
            Pal.GhostStmt("DllSeg.dll_seg_intro_cons 1.0R $(node) None $(tail) #nr #$(xs)");
            return node;
        }
    }
}
