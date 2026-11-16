module SortedSetInductive.RemoveDispatchClient
#lang-pulse

open Pulse.Lib.Pervasives
module O = SortedSetInductive.Ownership
module X = SortedSetInductive.RemoveDispatch
module W = SortedSetInductive.Borrow
module Q = SortedSetInductive.Rotation
module V = SortedSetInductive.Selector
module N = Class_Node
module D = Pulse.Lib.CSharp.TopDown
module R = Pulse.Lib.CSharp.TopDownRemove
module P = Pulse.Lib.CSharp.RegionPath
module T = Pulse.Lib.CSharp.Tree
module B = Pulse.Lib.Box

#set-options "--z3rlimit 10"

fn nested (#a: Type0) (root current sibling: N.class_Node a)
    (n: erased (O.tree a)) (dir: erased bool)
  requires O.owns (reveal n) 1.0R **
    pure (O.good n /\ root == P.top n /\ T.Branch? n /\
      current == P.top (Q.child n (not (reveal dir))) /\
      sibling == P.top (Q.child n dir) /\ T.Branch? (Q.child n dir) /\
      SortedSetInductive.RemoveRotation.can_rotate
        (W.choose dir (D.nred (T.left (Q.child n dir)))) n)
  returns pivot: N.class_Node__opt a
  ensures O.owns (R.rotn (W.choose dir (D.nred (T.left (Q.child n dir)))) n) 1.0R **
    pure (pivot == P.top (R.rotn (W.choose dir (D.nred (T.left (Q.child n dir)))) n))
{
  V.open_selector root sibling n dir;
  let rotation = Func_Node_GetRotation.func_Node_GetRotation a root current sibling;
  assert (pure (rotation == W.choose dir (D.nred (T.left (Q.child n dir)))));
  let pivot = Func_Node_Rotate.func_Node_Rotate a root rotation;
  X.close_dispatch root pivot n rotation;
  SortedSetInductive.Edit.change (R.rotn rotation n)
    (R.rotn (W.choose dir (D.nred (T.left (Q.child n dir)))) n);
  pivot
}

fn nested_recolored (#a: Type0) (root current sibling: N.class_Node a)
    (n: erased (O.tree a)) (dir: erased bool)
  requires O.owns (reveal n) 1.0R **
    pure (O.good n /\ root == P.top n /\ T.Branch? n /\ D.nred n /\
      current == P.top (Q.child n (not (reveal dir))) /\
      sibling == P.top (Q.child n dir) /\ T.Branch? (Q.child n dir) /\
      SortedSetInductive.RemoveRotation.can_rotate
        (W.choose dir (D.nred (T.left (Q.child n dir)))) n)
  returns pivot: N.class_Node__opt a
  ensures O.owns (W.colored n (W.choose dir (D.nred (T.left (Q.child n dir))))) 1.0R **
    pure (pivot == P.top (W.colored n (W.choose dir (D.nred (T.left (Q.child n dir))))))
{
  V.open_selector root sibling n dir;
  let rotation = Func_Node_GetRotation.func_Node_GetRotation a root current sibling;
  assert (pure (rotation == W.choose dir (D.nred (T.left (Q.child n dir)))));
  let pivot = Func_Node_Rotate.func_Node_Rotate a root rotation;
  let parent_value = B.op_Bang root;
  let pivot_value = B.op_Bang pivot;
  B.op_Colon_Equals pivot {pivot_value with N.fld_Color=parent_value.N.fld_Color};
  X.close_colored root pivot n rotation true;
  SortedSetInductive.Edit.change (W.colored n rotation)
    (W.colored n (W.choose dir (D.nred (T.left (Q.child n dir)))));
  pivot
}
