using PalLang;

namespace PalCSharp.Tests;

/// <summary>
/// §7.2's contortion detector for §12. The same two operations, written differently: the
/// null test is inverted and its branches swapped, the cursor is read into a local before
/// the recursive call, the locals are renamed and reordered, and the addition is written
/// the other way round. Nothing in the translator may have to change for this to verify.
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
        Pal.GhostStmt("DllSeg.dll_cases 1.0R $(cursor) $(back) $(final) #$(items)");
        if (cursor != null)
        {
            Pal.GhostStmt(
                "DllSeg.dll_seg_elim_cons 1.0R $(cursor) $(back) None $(final) #$(items)");
            Pal.GhostStmt(
                "with cr ctl. assert (DllSeg.dll_seg 1.0R cr.Class_DNode.fld_next $(cursor) None " +
                "$(final) ctl)");
            DNode? onward = cursor.next;
            int seen = Count(onward, cursor, final);
            Pal.GhostStmt("DllSeg.dll_seg_intro_cons 1.0R (Some?.v $(cursor)) None $(final) #cr #ctl");
            Pal.GhostStmt(
                "rewrite (DllSeg.dll_seg 1.0R (Some (Some?.v $(cursor))) cr.Class_DNode.fld_prev " +
                "None $(final) (FStar.Int32.v cr.Class_DNode.fld_value :: ctl)) " +
                "as (DllSeg.dll_seg 1.0R $(cursor) $(back) None $(final) $(items))");
            return 1 + seen;
        }
        else
        {
            return 0;
        }
    }

    [Requires("Dll.Whole(first, final, items)")]
    [Requires("items.Length > 0")]
    [Ensures("Dll.Whole(Result, final, SpecList.Cons(datum, items))")]
    public static DNode? Prepend(DNode? first, DNode? final, int datum,
                                 Ghost<SpecList<SpecInt>> items = default)
    {
        DNode fresh = new DNode { next = first, prev = null, value = datum };
        Pal.GhostStmt("with fr. assert (Pulse.Lib.Box.pts_to $(fresh) fr)");
        Pal.GhostStmt("DllSeg.dll_cases 1.0R $(first) None $(final) #$(items)");
        if (first != null)
        {
            Pal.GhostStmt("DllSeg.dll_seg_elim_cons 1.0R $(first) None None $(final) #$(items)");
            Pal.GhostStmt(
                "with br btl. assert (DllSeg.dll_seg 1.0R br.Class_DNode.fld_next $(first) None " +
                "$(final) btl)");
            first.prev = fresh;
            Pal.GhostStmt("with br'. assert (Pulse.Lib.Box.pts_to (Some?.v $(first)) br')");
            Pal.GhostStmt(
                "rewrite (DllSeg.dll_seg 1.0R br.Class_DNode.fld_next $(first) None $(final) btl) " +
                "as (DllSeg.dll_seg 1.0R br'.Class_DNode.fld_next (Some (Some?.v $(first))) None " +
                "$(final) btl)");
            Pal.GhostStmt("DllSeg.dll_seg_intro_cons 1.0R (Some?.v $(first)) None $(final) #br' #btl");
            Pal.GhostStmt(
                "rewrite (DllSeg.dll_seg 1.0R (Some (Some?.v $(first))) br'.Class_DNode.fld_prev " +
                "None $(final) (FStar.Int32.v br'.Class_DNode.fld_value :: btl)) " +
                "as (DllSeg.dll_seg 1.0R fr.Class_DNode.fld_next (Some $(fresh)) None $(final) $(items))");
            Pal.GhostStmt("DllSeg.dll_seg_intro_cons 1.0R $(fresh) None $(final) #fr #$(items)");
            return fresh;
        }
        else
        {
            Pal.GhostStmt("unreachable ()");
            return null;
        }
    }
}
