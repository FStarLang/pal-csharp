module SortedSetInductive.FrontierClient
#lang-pulse

open Pulse.Lib.Pervasives
module F = SortedSetInductive.Frontier
module O = SortedSetInductive.Ownership
module N = Class_Node
module T = Pulse.Lib.CSharp.Tree
module D = Pulse.Lib.CSharp.TopDown
module B = Pulse.Lib.Box
module M = SortedSetInductive.MergeFrontier
module R = Pulse.Lib.CSharp.TopDownRemove
module EQ = Pulse.Lib.CSharp.EqualityModel

#set-options "--z3rlimit 10"

fn is2 (a: Type0) {| equality_a: EQ.has_equality a |}
    (x: N.class_Node a) (#n: erased (O.tree a))
  preserves F.read_cells x n
  returns result: bool
  ensures pure (result == R.is2 n)
{
  unfold (F.read_cells x n);
  with v. _;
  F.snapshot_facts n v;
  M.read_facts n;
  let result = Func_Node_Is2Node.func_Node_Is2Node a x;
  fold (F.read_cells x n);
  result
}

fn merge2 (a: Type0) {| equality_a: EQ.has_equality a |}
    (x: N.class_Node a) (#n: erased (O.tree a))
  requires F.split_cells x n
  ensures M.after x n
{
  unfold (F.split_cells x n);
  with v vl vr. _;
  F.snapshot_facts n v;
  F.snapshot_facts (T.left n) vl;
  F.snapshot_facts (T.right n) vr;
  B.pts_to_not_null v.N.fld_Left;
  B.pts_to_not_null v.N.fld_Right;
  Func_Node_Merge2Nodes.func_Node_Merge2Nodes a x;
  fold (M.after x n);
}

// Exercise the real translated accessors, not replacement implementations.
fn is4 (a: Type0) {| equality_a: EQ.has_equality a |}
    (x: N.class_Node a) (#n: erased (O.tree a))
  preserves F.read_cells x n
  returns result: bool
  ensures pure (result == D.is4 n)
{
  unfold (F.read_cells x n);
  with v. _;
  F.optional_red (T.left n);
  F.optional_red (T.right n);
  let result = Func_Node_Is4Node.func_Node_Is4Node a x;
  fold (F.read_cells x n);
  result
}

fn split4 (a: Type0) {| equality_a: EQ.has_equality a |}
    (x: N.class_Node a) (#n: erased (O.tree a))
  requires F.split_cells x n
  ensures F.split_after x n
{
  unfold (F.split_cells x n);
  with v vl vr. _;
  F.snapshot_facts n v;
  F.snapshot_facts (T.left n) vl;
  F.snapshot_facts (T.right n) vr;
  B.pts_to_not_null v.N.fld_Left;
  B.pts_to_not_null v.N.fld_Right;
  Func_Node_Split4Node.func_Node_Split4Node a x;
  fold (F.split_after x n);
}
