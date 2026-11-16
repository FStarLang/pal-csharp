module SortedSetInductive.RetainedHolder
#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.SmallType
module O = SortedSetInductive.Ownership
module F = Pulse.Lib.CSharp.Ownership
module S = Class_SortedSet
module N = Class_Node
module B = Pulse.Lib.Box
module Q = SortedSetInductive.State
module C = SortedSetInductive.StateCorrespondence
module G = Pulse.Lib.GhostReference

#set-options "--z3rlimit 10"

// Only a non-node collection holder is packaged here. Every node, including
// both collections' retired nodes, remains in the recursive observable state.
let merged (#a: Type0) (old cloned: O.state a) (frame: O.frame_ref) : GTot (O.state a) =
  hide (O.active cloned,
    O.Frame frame
      (O.Forest (O.active old)
        (O.append_retired (O.retired_state old) (O.retired_state cloned))))

ghost fn transfer (#a: Type0) (previous: N.class_Node__opt a) (old: O.state a)
    (dummy: S.class_SortedSet a) (m: S.class_SortedSet__model a)
  requires O.owner previous old 1.0R ** S.class_SortedSet__inv dummy m
  returns result: O.state a
  ensures O.owner m.Struct_SortedSetModel.fld_Root result 1.0R **
    pure (O.active result == m.Struct_SortedSetModel.fld_Labels)
{
  unfold (S.class_SortedSet__inv dummy m);
  with r. assert (B.pts_to dummy r ** O.owner r.S.fld_root r.S.fld_ownershipState 1.0R);
  unfold (O.owner previous old 1.0R);
  unfold (O.owner r.S.fld_root r.S.fld_ownershipState 1.0R);
  let frame = G.alloc #O.frame_payload #small_type1 (O.Boxed dummy r);
  fold (O.frame_pred (O.Boxed dummy r) 1.0R);
  fold (O.frame_owns frame 1.0R);
  O.join_retired (O.retired_state old) (O.retired_state r.S.fld_ownershipState) 1.0R;
  fold (O.retained
    (O.Forest (O.active old)
      (O.append_retired (O.retired_state old) (O.retired_state r.S.fld_ownershipState))) 1.0R);
  fold (O.retained
    (O.Frame frame
      (O.Forest (O.active old)
        (O.append_retired (O.retired_state old) (O.retired_state r.S.fld_ownershipState)))) 1.0R);
  fold (O.owner m.Struct_SortedSetModel.fld_Root
    (merged old r.S.fld_ownershipState frame) 1.0R);
  merged old r.S.fld_ownershipState frame
}

let payload (a: Type0) = O.tree a & O.retired a
let state_of (#a: Type0) (value: payload a) : Tot (O.state a) = hide value
let payload_of (#a: Type0) (s: O.state a) : GTot (payload a) = reveal s

ghost fn transfer_payload (#a: Type0) (previous: N.class_Node__opt a) (old: O.state a)
    (dummy: S.class_SortedSet a) (m: S.class_SortedSet__model a) (adopted: N.class_Node__opt a)
  requires O.owner previous old 1.0R ** S.class_SortedSet__inv dummy m **
    pure (adopted == O.top (SortedSetInductive.Read.labels m))
  returns result: erased (payload a)
  ensures O.owner adopted (state_of (reveal result)) 1.0R **
    pure (O.active (state_of (reveal result)) == m.Struct_SortedSetModel.fld_Labels)
{
  let result = transfer previous old dummy m;
  unfold (O.owner m.Struct_SortedSetModel.fld_Root result 1.0R);
  fold (O.owner adopted result 1.0R);
  rewrite (O.owner adopted result 1.0R)
    as (O.owner adopted (state_of (reveal result)) 1.0R);
  result
}

// Sharing the transferred owner splits both retained collections and the
// actual dummy holder box/ghost witness; gathering recovers all of them.
ghost fn transfer_share_gather (#a: Type0) (previous: N.class_Node__opt a) (old: O.state a)
    (dummy: S.class_SortedSet a) (m: S.class_SortedSet__model a)
  requires O.owner previous old 1.0R ** S.class_SortedSet__inv dummy m
  returns result: O.state a
  ensures O.owner m.Struct_SortedSetModel.fld_Root result 1.0R **
    pure (O.active result == m.Struct_SortedSetModel.fld_Labels)
{
  let result = transfer previous old dummy m;
  O.share_owner m.Struct_SortedSetModel.fld_Root result 1.0R ();
  O.gather_owner m.Struct_SortedSetModel.fld_Root result (1.0R /. 2.0R) (1.0R /. 2.0R) ();
  rewrite (O.owner m.Struct_SortedSetModel.fld_Root result
      ((1.0R /. 2.0R) +. (1.0R /. 2.0R)))
    as (O.owner m.Struct_SortedSetModel.fld_Root result 1.0R);
  result
}

let frame_observation (#a: Type0) (t: O.tree a) (rest: O.retired a)
    (frame: O.frame_ref)
  : Lemma (
    Q.observe (hide (t, O.Frame frame rest)) ==
    Q.observe (hide (t, rest))) =
  Q.observation_equal
    (Q.observe (hide (t, O.Frame frame rest)))
    (Q.observe (hide (t, rest)))

let transferred_correspondence (#a: Type0) (old cloned: O.state a)
    (frame: O.frame_ref) (x: N.class_Node__opt a)
  : Lemma (
    Q.tree_at (Q.observe (merged old cloned frame)) x ==
      Pulse.Lib.CSharp.Region.tree_of C.view O.left O.right (C.reference_state (merged old cloned frame)) x /\
    (Q.wf (Q.observe (merged old cloned frame)) x <==>
      Pulse.Lib.CSharp.Region.wf O.left O.right (C.reference_state (merged old cloned frame)) x)) =
  C.state_current_tree (merged old cloned frame) x
