module SortedSetInductive.RotationClient
#lang-pulse

open Pulse.Lib.Pervasives
module O = SortedSetInductive.Ownership
module R = SortedSetInductive.Rotation
module N = Class_Node
module T = Pulse.Lib.CSharp.Tree
module P = Pulse.Lib.CSharp.RegionPath

#set-options "--z3rlimit 10"

// The original conditional expression calls the actual verified C# methods.
// This client checks that opening/closing can surround the whole expression.
fn single (#a: Type0) (root: N.class_Node a) (right: bool) (#n: erased (O.tree a))
  requires O.owns n 1.0R ** pure (root == P.top n /\ T.Branch? n /\ T.Branch? (R.child n right))
  returns result: N.class_Node a
  ensures O.owns (R.single n right) 1.0R ** pure (result == P.top (R.single n right))
{
  R.open_single root n right;
  let result =
    if right {
      Func_Node_RotateLeft.func_Node_RotateLeft a root
    } else {
      Func_Node_RotateRight.func_Node_RotateRight a root
    };
  R.close_single root result n right;
  result
}

fn double (#a: Type0) (root: N.class_Node a) (right: bool) (#n: erased (O.tree a))
  requires O.owns n 1.0R **
    pure (root == P.top n /\ T.Branch? n /\ T.Branch? (R.double_child n right) /\ T.Branch? (R.grand n right))
  returns result: N.class_Node a
  ensures O.owns (R.double n right) 1.0R ** pure (result == P.top (R.double n right))
{
  R.open_double root n right;
  let result =
    if right {
      Func_Node_RotateLeftRight.func_Node_RotateLeftRight a root
    } else {
      Func_Node_RotateRightLeft.func_Node_RotateRightLeft a root
    };
  R.close_double root result n right;
  result
}
