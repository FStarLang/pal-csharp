module SortedSetInductive.State

module O = SortedSetInductive.Ownership
module N = Class_Node
module B = Pulse.Lib.Box
module T = Pulse.Lib.CSharp.Tree
module E = Pulse.Lib.CSharp.RefEq
module Seq = FStar.Seq
module W = Pulse.Lib.CSharp.RegionWalk
module FE = FStar.FunctionalExtensionality

#set-options "--z3rlimit 10"

// This is an observation of recursive ownership, not an ownership map.
// In particular, a retired Cell's links are interpreted against the CURRENT
// whole state, not against a frozen tree saved at retirement.
let record (#a: Type0) (l: O.tree a)
    (e: N.class_Node__opt a & (a & bool)) (r: O.tree a) : N.class_Node__raw a =
  { N.fld_Item = fst (snd e); N.fld_Color = O.color (snd (snd e));
    N.fld_Left = O.top l; N.fld_Right = O.top r }

let rec find_tree (#a: Type0) (t: O.tree a) (x: N.class_Node__opt a)
  : Tot (option (N.class_Node__raw a)) (decreases t) =
  match t with
  | T.Leaf -> None
  | T.Branch l e r ->
    if E.ref_eq (fst e) x then Some (record l e r)
    else match find_tree l x with
         | Some v -> Some v
         | None -> find_tree r x

let find_tree_step (#a: Type0) (l r: O.tree a)
    (e: N.class_Node__opt a & (a & bool)) (x: N.class_Node__opt a)
  : Lemma (find_tree (T.Branch l e r) x ==
      (if E.ref_eq (fst e) x then Some (record l e r)
       else match find_tree l x with | Some v -> Some v | None -> find_tree r x)) = ()

let rec count_retired (#a: Type0) (r: O.retired a) : Tot nat (decreases r) =
  match r with
  | O.End -> 0
  | O.Cell _ _ rest -> 1 + count_retired rest
  | O.Forest t rest -> T.size t + count_retired rest
  | O.Frame _ rest -> count_retired rest

let rec find_retired (#a: Type0) (r: O.retired a) (x: N.class_Node__opt a)
  : Tot (option (N.class_Node__raw a)) (decreases r) =
  match r with
  | O.End -> None
  | O.Cell y v rest -> if E.ref_eq y x then Some v else find_retired rest x
  | O.Frame _ rest -> find_retired rest x
  | O.Forest t rest ->
    match find_tree t x with
    | Some v -> Some v
    | None -> find_retired rest x

let find_parts (#a: Type0) (t: O.tree a) (r: O.retired a) (x: N.class_Node__opt a) =
  match find_tree t x with
  | Some v -> Some v
  | None -> find_retired r x

// Count includes every represented cell, exactly as the baseline fuel did.
// Neither active size nor distinct-address cardinality is a replacement.
let observation (a: Type0) =
  nat & FE.restricted_t (N.class_Node__opt a) (fun _ -> option (N.class_Node__raw a))

let observe (#a: Type0) (s: O.state a) : GTot (observation a) =
  let t = O.active s in
  let r = O.retired_state s in
  T.size t + count_retired r, FE.on (N.class_Node__opt a) (find_parts t r)

let find (#a: Type0) (h: observation a) (x: N.class_Node__opt a) = snd h x
let mem (#a: Type0) (h: observation a) (x: N.class_Node__opt a) = Some? (find h x)
let get (#a: Type0) (h: observation a) (x: N.class_Node__opt a{mem h x}) = Some?.v (find h x)
let fuel (#a: Type0) (h: observation a) = fst h + 1

let equivalent (#a: Type0) (h k: observation a) : prop =
  fst h == fst k /\ (forall x. find h x == find k x)

// Restriction to the pointer domain makes observational equality actual model
// equality using F*'s standard functional-extensionality library. No private
// retired constructor, grouping, or witness identity is exposed in the model.
let observation_equal (#a: Type0) (h k: observation a)
  : Lemma (requires equivalent h k) (ensures h == k) =
  FE.extensionality (N.class_Node__opt a) (fun _ -> option (N.class_Node__raw a))
    (snd h) (snd k)

let rec tree_n (#a: Type0) (n: nat) (h: observation a) (x: N.class_Node__opt a)
  : Tot (T.tree (a & bool)) (decreases n) =
  if n = 0 || B.is_null x then T.Leaf
  else match find h x with
       | None -> T.Leaf
       | Some r -> T.Branch (tree_n (n - 1) h (O.left r)) (O.entry r)
                           (tree_n (n - 1) h (O.right r))

let rec closed (#a: Type0) (n: nat) (h: observation a) (x: N.class_Node__opt a)
  : Tot prop (decreases n) =
  B.is_null x \/
  (n > 0 /\ mem h x /\ closed (n - 1) h (O.left (get h x)) /\
                        closed (n - 1) h (O.right (get h x)))

[@@"opaque_to_smt"]
let tree_at (#a: Type0) (h: observation a) (x: N.class_Node__opt a) =
  tree_n (fuel h) h x

[@@"opaque_to_smt"]
let wf (#a: Type0) (h: observation a) (x: N.class_Node__opt a) =
  closed (fuel h) h x

let root_step (#a: Type0) (h: observation a) (x: N.class_Node__opt a)
  : Lemma (requires mem h x /\ not (B.is_null x))
      (ensures tree_at h x ==
        T.Branch (tree_n (fst h) h (O.left (get h x))) (O.entry (get h x))
                 (tree_n (fst h) h (O.right (get h x)))) =
  reveal_opaque (`%tree_at) (tree_at #a)

// Public consequences of the opaque interpretation, without exposing
// recursive pointer traversal to each caller's solver.
let member_nonempty (#a: Type0) (h: observation a) (x: N.class_Node__opt a)
  : Lemma (requires mem h x /\ not (B.is_null x))
      (ensures not (T.Leaf? (tree_at h x)))
      [SMTPat (mem h x)] =
  root_step h x

let well_formed_member (#a: Type0) (h: observation a) (x: N.class_Node__opt a)
  : Lemma (requires wf h x)
      (ensures B.is_null x \/ mem h x)
      [SMTPat (wf h x)] =
  reveal_opaque (`%wf) (wf #a)

let entry (#a: Type0) (rev: bool) (h: observation a) (x: N.class_Node__opt a) =
  match tree_at h x with
  | T.Leaf -> Seq.empty
  | T.Branch l (k, _) r -> Seq.cons k (W.okeys rev (if rev then l else r))

let rec pending (#a: Type0) (rev: bool) (h: observation a)
    (s: Seq.seq (N.class_Node__opt a)) : Tot (Seq.seq a) (decreases Seq.length s) =
  if Seq.length s = 0 then Seq.empty
  else let n = Seq.length s - 1 in
       Seq.append (entry rev h (Seq.index s n)) (pending rev h (Seq.slice s 0 n))

let walkable (#a: Type0) (h: observation a) (s: Seq.seq (N.class_Node__opt a)) : prop =
  forall (i: nat). {:pattern Seq.index s i}
    i < Seq.length s ==> wf h (Seq.index s i) /\ not (B.is_null (Seq.index s i))

let rec tree_n_equivalent (#a: Type0) (n: nat) (h k: observation a) (x: N.class_Node__opt a)
  : Lemma (requires forall y. find h y == find k y)
      (ensures tree_n n h x == tree_n n k x /\ (closed n h x <==> closed n k x))
      (decreases n) =
  if n = 0 || B.is_null x then ()
  else match find h x with
       | None -> ()
       | Some r ->
         tree_n_equivalent (n - 1) h k (O.left r);
         tree_n_equivalent (n - 1) h k (O.right r)

let tree_equivalent (#a: Type0) (h k: observation a) (x: N.class_Node__opt a)
  : Lemma (requires equivalent h k)
      (ensures tree_at h x == tree_at k x /\ (wf h x <==> wf k x)) =
  reveal_opaque (`%tree_at) (tree_at #a);
  reveal_opaque (`%wf) (wf #a);
  tree_n_equivalent (fuel h) h k x
