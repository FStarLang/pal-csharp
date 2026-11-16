module SortedSetInductive.StateCorrespondence

module O = SortedSetInductive.Ownership
module Q = SortedSetInductive.State
module R = Pulse.Lib.CSharp.Region
module W = Pulse.Lib.CSharp.RegionWalk
module N = Class_Node
module B = Pulse.Lib.Box
module Seq = FStar.Seq
module T = Pulse.Lib.CSharp.Tree

#set-options "--z3rlimit 10"

// Only the baseline's PURE interpretation is used here. No ownership
// conversion or new axiom occurs in this module.
let view (#a: Type0) (_: N.class_Node__opt a) (v: N.class_Node__raw a) = O.entry v

let agrees (#a: Type0) (q: Q.observation a) (h: R.heap (N.class_Node__raw a)) =
  fst q == FStar.List.Tot.length h /\ (forall x. Q.find q x == R.lookup h x)

// A proof-only serialization supplies the correspondence witness for EVERY
// recursive state. No implementation or ownership predicate uses this list.
let rec reference_tree (#a: Type0) (t: O.tree a) : Tot (R.heap (N.class_Node__raw a)) (decreases t) =
  match t with
  | T.Leaf -> []
  | T.Branch l e r ->
    (fst e, Q.record l e r) :: FStar.List.Tot.append (reference_tree l) (reference_tree r)

let rec reference_retired (#a: Type0) (r: O.retired a) : Tot (R.heap (N.class_Node__raw a)) (decreases r) =
  match r with
  | O.End -> []
  | O.Cell x v rest -> (x, v) :: reference_retired rest
  | O.Forest t rest -> FStar.List.Tot.append (reference_tree t) (reference_retired rest)
  | O.Frame _ rest -> reference_retired rest

let reference_state (#a: Type0) (s: O.state a) : GTot (R.heap (N.class_Node__raw a)) =
  FStar.List.Tot.append (reference_tree (O.active s)) (reference_retired (O.retired_state s))

let rec lookup_append (#a: Type0) (h k: R.heap (N.class_Node__raw a)) (x: N.class_Node__opt a)
  : Lemma (ensures R.lookup (FStar.List.Tot.append h k) x ==
    (match R.lookup h x with | Some v -> Some v | None -> R.lookup k x)) (decreases h) =
  match h with
  | [] -> ()
  | _ :: rest -> lookup_append rest k x

let lookup_cons (#a: Type0) (y x: N.class_Node__opt a) (v: N.class_Node__raw a)
    (h: R.heap (N.class_Node__raw a))
  : Lemma (R.lookup ((y, v) :: h) x == (if R.eq_box y x then Some v else R.lookup h x)) = ()

let length_cons (#a: Type0) (x: a) (xs: list a)
  : Lemma (FStar.List.Tot.length (x :: xs) == 1 + FStar.List.Tot.length xs) = ()

let size_branch (#a: Type0) (l r: O.tree a) (e: N.class_Node__opt a & (a & bool))
  : Lemma (T.size (T.Branch l e r) == 1 + T.size l + T.size r) = ()

#push-options "--fuel 1 --ifuel 1"
let rec tree_reference (#a: Type0) (t: O.tree a) (x: N.class_Node__opt a)
  : Lemma (ensures R.lookup (reference_tree t) x == Q.find_tree t x /\
      FStar.List.Tot.length (reference_tree t) == T.size t) (decreases t) =
  match t with
  | T.Leaf -> ()
  | T.Branch l e r ->
    tree_reference l x; tree_reference r x;
    lookup_append (reference_tree l) (reference_tree r) x;
    FStar.List.Tot.Properties.append_length (reference_tree l) (reference_tree r);
    assert (reference_tree t ==
      (fst e, Q.record l e r) :: FStar.List.Tot.append (reference_tree l) (reference_tree r));
    length_cons (fst e, Q.record l e r)
      (FStar.List.Tot.append (reference_tree l) (reference_tree r));
    size_branch l r e;
    lookup_cons (fst e) x (Q.record l e r)
      (FStar.List.Tot.append (reference_tree l) (reference_tree r));
    Q.find_tree_step l r e x;
    if R.eq_box (fst e) x then ()
    else match Q.find_tree l x with | Some _ -> () | None -> ()
#pop-options

let rec retired_reference (#a: Type0) (r: O.retired a) (x: N.class_Node__opt a)
  : Lemma (ensures R.lookup (reference_retired r) x == Q.find_retired r x /\
      FStar.List.Tot.length (reference_retired r) == Q.count_retired r) (decreases r) =
  match r with
  | O.End -> ()
  | O.Cell _ _ rest -> retired_reference rest x
  | O.Frame _ rest -> retired_reference rest x
  | O.Forest t rest ->
    tree_reference t x; retired_reference rest x;
    lookup_append (reference_tree t) (reference_retired rest) x;
    FStar.List.Tot.Properties.append_length (reference_tree t) (reference_retired rest)

let state_reference (#a: Type0) (s: O.state a)
  : Lemma (agrees (Q.observe s) (reference_state s)) =
  let at (x: N.class_Node__opt a) : Lemma
      (Q.find (Q.observe s) x == R.lookup (reference_state s) x) =
    tree_reference (O.active s) x;
    retired_reference (O.retired_state s) x;
    lookup_append (reference_tree (O.active s)) (reference_retired (O.retired_state s)) x in
  FStar.Classical.forall_intro at;
  tree_reference (O.active s) B.null;
  retired_reference (O.retired_state s) B.null;
  FStar.List.Tot.Properties.append_length
    (reference_tree (O.active s)) (reference_retired (O.retired_state s))

let rec bounded (#a: Type0) (n: nat) (q: Q.observation a)
    (h: R.heap (N.class_Node__raw a)) (x: N.class_Node__opt a)
  : Lemma (requires forall y. Q.find q y == R.lookup h y)
      (ensures Q.tree_n n q x == R.tree_n view O.left O.right n h x /\
        (Q.closed n q x <==> R.closed O.left O.right n h x))
      (decreases n) =
  if n = 0 || B.is_null x then ()
  else match Q.find q x with
       | None -> ()
       | Some r ->
         bounded (n - 1) q h (O.left r);
         bounded (n - 1) q h (O.right r)

let current_tree (#a: Type0) (q: Q.observation a)
    (h: R.heap (N.class_Node__raw a)) (x: N.class_Node__opt a)
  : Lemma (requires agrees q h)
      (ensures Q.tree_at q x == R.tree_of view O.left O.right h x /\
        (Q.wf q x <==> R.wf O.left O.right h x)) =
  reveal_opaque (`%Q.tree_at) (Q.tree_at #a);
  reveal_opaque (`%Q.wf) (Q.wf #a);
  reveal_opaque (`%R.tree_of) (R.tree_of #(N.class_Node__raw a) #(a & bool));
  reveal_opaque (`%R.wf) (R.wf #(N.class_Node__raw a));
  bounded (Q.fuel q) q h x

let state_current_tree (#a: Type0) (s: O.state a) (x: N.class_Node__opt a)
  : Lemma (Q.tree_at (Q.observe s) x == R.tree_of view O.left O.right (reference_state s) x /\
      (Q.wf (Q.observe s) x <==> R.wf O.left O.right (reference_state s) x)) =
  state_reference s;
  current_tree (Q.observe s) (reference_state s) x

let rec pending (#a: Type0) (rev: bool) (q: Q.observation a)
    (h: R.heap (N.class_Node__raw a)) (s: Seq.seq (N.class_Node__opt a))
  : Lemma (requires agrees q h)
      (ensures Seq.equal (Q.pending rev q s) (W.pending view O.left O.right rev h s))
      (decreases Seq.length s) =
  if Seq.length s = 0 then ()
  else (
    let n = Seq.length s - 1 in
    current_tree q h (Seq.index s n);
    pending rev q h (Seq.slice s 0 n))

let walkable (#a: Type0) (q: Q.observation a)
    (h: R.heap (N.class_Node__raw a)) (s: Seq.seq (N.class_Node__opt a))
  : Lemma (requires agrees q h)
      (ensures Q.walkable q s <==> W.walkable view O.left O.right h s) =
  let at (i: nat) : Lemma
      (i < Seq.length s ==>
        (Q.wf q (Seq.index s i) <==> R.wf O.left O.right h (Seq.index s i))) =
    if i < Seq.length s then current_tree q h (Seq.index s i) in
  FStar.Classical.forall_intro at
