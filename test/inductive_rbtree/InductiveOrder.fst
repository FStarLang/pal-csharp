module InductiveOrder

module M = InductiveModel
module T = Pulse.Lib.CSharp.Tree
module ST = Pulse.Lib.CSharp.SearchTree
module O = Pulse.Lib.CSharp.Order
module Seq = FStar.Seq
module C = FStar.Classical

#set-options "--z3rlimit 10"

// Quantification over stored keys, independent of the search algorithm.
let rec every (#a: Type0) (p: a -> prop) (t: M.tree a) : Tot prop (decreases t) =
  match t with
  | T.Leaf -> True
  | T.Branch l (k, _) r -> every p l /\ p k /\ every p r

let rec every_keys (#a: Type0) (p: a -> prop) (t: M.tree a)
  : Lemma
    (ensures every p t <==>
      (forall (i: nat). i < Seq.length (ST.keys t) ==> p (Seq.index (ST.keys t) i)))
    (decreases t)
  = match t with
    | T.Leaf -> ()
    | T.Branch l (k, _) r ->
      every_keys p l;
      every_keys p r;
      let kl = ST.keys l in
      let kr = ST.keys r in
      let s = ST.keys t in
      C.forall_intro (ST.index_pivot kl k kr);
      let fwd () : Lemma
        (requires every p t)
        (ensures forall (i: nat). i < Seq.length s ==> p (Seq.index s i))
        = let at (i: nat) : Lemma (i < Seq.length s ==> p (Seq.index s i)) =
            if i < Seq.length kl then ()
            else if i = Seq.length kl then ()
            else ()
          in C.forall_intro at
      in
      let bwd () : Lemma
        (requires forall (i: nat). i < Seq.length s ==> p (Seq.index s i))
        (ensures every p t)
        = assert (Seq.index s (Seq.length kl) == k);
          assert (forall (i: nat). i < Seq.length kl ==> Seq.index s i == Seq.index kl i);
          assert (forall (i: nat). i < Seq.length kr ==>
            Seq.index s (Seq.length kl + 1 + i) == Seq.index kr i)
      in
      C.move_requires fwd ();
      C.move_requires bwd ()

let member (#a: Type0) (c: O.comparer a) (t: M.tree a) (x: a) : prop =
  not (every (fun y -> O.compare c x y <> 0) t)

let adds_exactly (#a: Type0) (c: O.comparer a) (t: M.tree a) (k: a) (u: M.tree a) : prop =
  if ST.contains c t k then Seq.equal (ST.keys u) (ST.keys t)
  else forall (x: a). member c u x <==> (member c t x \/ O.compare c x k == 0)

let removes_exactly (#a: Type0) (c: O.comparer a) (t: M.tree a) (k: a) (u: M.tree a) : prop =
  if not (ST.contains c t k) then Seq.equal (ST.keys u) (ST.keys t)
  else exists (pre post: Seq.seq a) (pivot: a).
    O.compare c k pivot == 0 /\
    Seq.equal (ST.keys t) (Seq.append pre (Seq.cons pivot post)) /\
    Seq.equal (ST.keys u) (Seq.append pre post)
