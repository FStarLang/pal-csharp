module SortedSetInductive.Lift

module C = SortedSetInductive.Ownership
module N = Class_Node
module P = Pulse.Lib.CSharp.RegionPath
module D = Pulse.Lib.CSharp.TopDown
module T = Pulse.Lib.CSharp.Tree
module S = Pulse.Lib.CSharp.SearchTree
module M = SortedSetInductive.Mutation
module B = Pulse.Lib.Box

#set-options "--z3rlimit 10"

let child (#a: Type0) (n: C.tree a) (x: N.class_Node__opt a) =
  T.Branch? n /\ x =!= B.null /\ (x == P.top (T.left n) \/ x == P.top (T.right n))
let right (#a: Type0) (n: C.tree a) (x: N.class_Node__opt a) =
  Pulse.Lib.CSharp.RefEq.ref_eq (P.top (T.right n)) x
let rotated (#a: Type0) (n: C.tree a) (x: N.class_Node__opt a) =
  if right n x then S.rot_left n else S.rot_right n
let lifted (#a: Type0) (n: C.tree a) (x: N.class_Node__opt a) =
  D.recolorn (M.recolor (rotated n x) (P.top n) true) false
let whole (#a: Type0) (n: C.tree a) (p x: N.class_Node__opt a) =
  P.replace n p (lifted (P.sub n p) x)

let layout (#a: Type0) (n: C.tree a) (x: N.class_Node__opt a)
  : Lemma (requires C.good n /\ child n x)
      (ensures
        (if right n x then T.Branch? (T.right n) else T.Branch? (T.left n)) /\
        P.top (rotated n x) == x /\ C.member (rotated n x) (P.top n))
  = let T.Branch l _ r = n in
    if right n x then (
      assert (T.Branch? r);
      let T.Branch _ _ _ = r in ())
    else (
      assert (T.Branch? l);
      let T.Branch _ _ _ = l in ())
