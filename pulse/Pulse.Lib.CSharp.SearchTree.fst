module Pulse.Lib.CSharp.SearchTree

/// The comparer-directed searches of a binary search tree whose nodes carry a key and a
/// tag (a red-black tree's colour) (doc/translation.md R27.9). Each function follows the
/// path the code follows, so what it says needs no ordering hypothesis: it is what the
/// search returns, whatever the tree.

module O = Pulse.Lib.CSharp.Order
module T = Pulse.Lib.CSharp.Tree

/// Whether the search for `x` ends at a node whose key compares equal to it.
let rec contains (#a #b: Type0) (c: O.comparer a) (t: T.tree (a & b)) (x: a)
  : Tot bool (decreases t)
  = match t with
    | T.Leaf -> false
    | T.Branch l (v, _) r ->
      let o = O.compare c x v in
      if o = 0 then true else if o < 0 then contains c l x else contains c r x

/// The key the search for `x` ends at, or `d` when it ends at a leaf.
let rec find (#a #b: Type0) (c: O.comparer a) (t: T.tree (a & b)) (x: a) (d: a)
  : Tot a (decreases t)
  = match t with
    | T.Leaf -> d
    | T.Branch l (v, _) r ->
      let o = O.compare c x v in
      if o = 0 then v else if o < 0 then find c l x d else find c r x d

/// The leftmost key, or `d` in the empty tree.
let rec leftmost (#a #b: Type0) (t: T.tree (a & b)) (d: a) : Tot a (decreases t) =
  match t with
  | T.Leaf -> d
  | T.Branch T.Leaf (v, _) _ -> v
  | T.Branch l _ _ -> leftmost l d

/// The rightmost key, or `d` in the empty tree.
let rec rightmost (#a #b: Type0) (t: T.tree (a & b)) (d: a) : Tot a (decreases t) =
  match t with
  | T.Leaf -> d
  | T.Branch _ (v, _) T.Leaf -> v
  | T.Branch _ _ r -> rightmost r d

/// The position of the node the search for `x` ends at, numbering the tree breadth-first
/// as an implicit binary heap is numbered (the root of a subtree being `k`), or -1.
let rec heap_index (#a #b: Type0) (c: O.comparer a) (t: T.tree (a & b)) (x: a) (k: int)
  : Tot int (decreases t)
  = match t with
    | T.Leaf -> -1
    | T.Branch l (v, _) r ->
      let o = O.compare c x v in
      if o = 0 then k
      else if o < 0 then heap_index c l x (2 * k + 1)
      else heap_index c r x (2 * k + 2)

(* ---------------------------------------------------------------------------------- *)
(* R27.11. The set a search tree holds, and the red-black invariants.                   *)

module Seq = FStar.Seq
module S = Pulse.Lib.CSharp.Sorted

/// The keys in order: the set's model, once they are strictly sorted.
let rec keys (#a #b: Type0) (t: T.tree (a & b)) : Tot (Seq.seq a) (decreases t) =
  match t with
  | T.Leaf -> Seq.empty
  | T.Branch l (v, _) r -> Seq.append (keys l) (Seq.cons v (keys r))

let rec keys_length (#a #b: Type0) (t: T.tree (a & b))
  : Lemma (ensures Seq.length (keys t) == T.size t) (decreases t)
          [SMTPat (Seq.length (keys t))]
  = match t with
    | T.Leaf -> ()
    | T.Branch l _ r -> keys_length l; keys_length r

/// A node's tag is whether it is red.
let is_red (#a: Type0) (t: T.tree (a & bool)) : bool =
  match t with
  | T.Branch _ (_, red) _ -> red
  | T.Leaf -> false

/// The number of black nodes on the leftmost path.
let rec black_height (#a: Type0) (t: T.tree (a & bool)) : Tot nat (decreases t) =
  match t with
  | T.Leaf -> 0
  | T.Branch l (_, red) _ -> black_height l + (if red then 0 else 1)

/// No red node has a red child, and every path has the same number of black nodes.
let rec rb (#a: Type0) (t: T.tree (a & bool)) : Tot bool (decreases t) =
  match t with
  | T.Leaf -> true
  | T.Branch l (_, red) r ->
    rb l && rb r && black_height l = black_height r &&
    (not red || (not (is_red l) && not (is_red r)))

/// A red-black tree: `rb`, with a black root.
let red_black (#a: Type0) (t: T.tree (a & bool)) : bool = rb t && not (is_red t)

let below_all (#a: Type0) (c: O.comparer a) (s: Seq.seq a) (v: a) : prop =
  forall (i: nat). i < Seq.length s ==> O.compare c (Seq.index s i) v < 0

let above_all (#a: Type0) (c: O.comparer a) (v: a) (s: Seq.seq a) : prop =
  forall (i: nat). i < Seq.length s ==> O.compare c v (Seq.index s i) < 0

let index_pivot (#a: Type0) (sl: Seq.seq a) (v: a) (sr: Seq.seq a) (i: nat)
  : Lemma (ensures i < Seq.length (Seq.append sl (Seq.cons v sr)) ==>
                   Seq.index (Seq.append sl (Seq.cons v sr)) i ==
                   (if i < Seq.length sl then Seq.index sl i
                    else if i = Seq.length sl then v
                    else Seq.index sr (i - Seq.length sl - 1)))
  = ()

/// A node's keys are strictly sorted exactly when its subtrees' are and the key separates them.
let sorted_pivot (#a: Type0) (c: O.comparer a) (sl: Seq.seq a) (v: a) (sr: Seq.seq a)
  : Lemma (S.strictly_sorted c (Seq.append sl (Seq.cons v sr)) <==>
           (S.strictly_sorted c sl /\ S.strictly_sorted c sr /\
            below_all c sl v /\ above_all c v sr))
  = let s = Seq.append sl (Seq.cons v sr) in
    let n = Seq.length sl in
    FStar.Classical.forall_intro (index_pivot sl v sr);
    let fwd () : Lemma (requires S.strictly_sorted c s)
                       (ensures S.strictly_sorted c sl /\ S.strictly_sorted c sr /\
                                below_all c sl v /\ above_all c v sr)
      = assert (forall (i: nat). i < n ==> Seq.index s i == Seq.index sl i);
        assert (forall (i: nat). i < Seq.length sr ==> Seq.index s (n + 1 + i) == Seq.index sr i);
        assert (Seq.index s n == v)
    in
    let bwd () : Lemma (requires S.strictly_sorted c sl /\ S.strictly_sorted c sr /\
                                 below_all c sl v /\ above_all c v sr)
                       (ensures S.strictly_sorted c s)
      = let aux (i j: nat)
          : Lemma (ensures i < j /\ j < Seq.length s ==> O.compare c (Seq.index s i) (Seq.index s j) < 0)
          = if not (i < j && j < Seq.length s) then ()
            else if j < n then ()
            else if i < n && j = n then ()
            else if i = n then ()
            else if i < n then
              O.compare_trans c (Seq.index sl i) v (Seq.index sr (j - n - 1))
            else ()
        in
        FStar.Classical.forall_intro_2 aux
    in
    FStar.Classical.move_requires fwd ();
    FStar.Classical.move_requires bwd ()

let sorted_branch (#a #b: Type0) (c: O.comparer a) (l: T.tree (a & b)) (v: a) (g: b) (r: T.tree (a & b))
  : Lemma (S.strictly_sorted c (keys (T.Branch l (v, g) r)) <==>
           (S.strictly_sorted c (keys l) /\ S.strictly_sorted c (keys r) /\
            below_all c (keys l) v /\ above_all c v (keys r)))
          [SMTPat (S.strictly_sorted c (keys (T.Branch l (v, g) r)))]
  = sorted_pivot c (keys l) v (keys r)

let rec lower_bound_append (#a: Type0) (c: O.comparer a) (s1 s2: Seq.seq a) (x: a)
  : Lemma (ensures S.lower_bound c (Seq.append s1 s2) x == S.lower_bound c s1 x + S.lower_bound c s2 x)
          (decreases Seq.length s1)
  = if Seq.length s1 = 0 then assert (Seq.equal (Seq.append s1 s2) s2)
    else (assert (Seq.equal (Seq.tail (Seq.append s1 s2)) (Seq.append (Seq.tail s1) s2));
          lower_bound_append c (Seq.tail s1) s2 x)

let rec lower_bound_all_below (#a: Type0) (c: O.comparer a) (s: Seq.seq a) (x: a)
  : Lemma (requires forall (i: nat). i < Seq.length s ==> O.compare c (Seq.index s i) x < 0)
          (ensures S.lower_bound c s x == Seq.length s)
          (decreases Seq.length s)
  = if Seq.length s = 0 then () else lower_bound_all_below c (Seq.tail s) x

let rec lower_bound_all_above (#a: Type0) (c: O.comparer a) (s: Seq.seq a) (x: a)
  : Lemma (requires forall (i: nat). i < Seq.length s ==> O.compare c (Seq.index s i) x >= 0)
          (ensures S.lower_bound c s x == 0)
          (decreases Seq.length s)
  = if Seq.length s = 0 then () else lower_bound_all_above c (Seq.tail s) x

/// Where the search for `x` goes in a node whose keys are sorted: the position the node's
/// key or one of its subtrees gives, shifted to the node's sequence.
let lower_bound_pivot (#a: Type0) (c: O.comparer a) (sl: Seq.seq a) (v: a) (sr: Seq.seq a) (x: a)
  : Lemma (requires below_all c sl v /\ above_all c v sr)
          (ensures (let lb = S.lower_bound c (Seq.append sl (Seq.cons v sr)) x in
                    let o = O.compare c x v in
                    (o = 0 ==> lb == Seq.length sl) /\
                    (o < 0 ==> lb == S.lower_bound c sl x) /\
                    (o > 0 ==> lb == Seq.length sl + 1 + S.lower_bound c sr x)))
  = let o = O.compare c x v in
    lower_bound_append c sl (Seq.cons v sr) x;
    lower_bound_append c (Seq.create 1 v) sr x;
    assert (Seq.equal (Seq.cons v sr) (Seq.append (Seq.create 1 v) sr));
    assert (S.lower_bound c (Seq.tail (Seq.create 1 v)) x == 0);
    let gt_v (y: a) : Lemma (requires O.compare c v y < 0 /\ o <= 0) (ensures O.compare c y x > 0)
      = O.compare_antisym c x v; O.compare_antisym c y x;
        O.compare_trans c x v y; O.compare_antisym c x y in
    let lt_v (y: a) : Lemma (requires O.compare c y v < 0 /\ o >= 0) (ensures O.compare c y x < 0)
      = O.compare_antisym c x v; O.compare_trans c y v x in
    if o <= 0 then begin
      FStar.Classical.forall_intro (FStar.Classical.move_requires gt_v);
      lower_bound_all_above c sr x
    end;
    if o >= 0 then begin
      FStar.Classical.forall_intro (FStar.Classical.move_requires lt_v);
      lower_bound_all_below c sl x
    end

/// R27.11. On a tree whose keys are strictly sorted, the search finds exactly the members:
/// the node it ends at holds the key at `x`'s position in the in-order sequence.
let rec find_keys (#a #b: Type0) (c: O.comparer a) (t: T.tree (a & b)) (x d: a)
  : Lemma (requires S.strictly_sorted c (keys t))
          (ensures (let i = S.key_index c (keys t) x in
                    contains c t x == (i >= 0) /\
                    find c t x d == (if i >= 0 then Seq.index (keys t) i else d)))
          (decreases t)
  = match t with
    | T.Leaf -> ()
    | T.Branch l (v, g) r ->
      let sl = keys l in
      let sr = keys r in
      let n = Seq.length sl in
      sorted_pivot c sl v sr;
      lower_bound_pivot c sl v sr x;
      FStar.Classical.forall_intro (index_pivot sl v sr);
      let o = O.compare c x v in
      O.compare_antisym c x v;
      if o = 0 then ()
      else if o < 0 then find_keys c l x d
      else find_keys c r x d

let contains_keys (#a #b: Type0) (c: O.comparer a) (t: T.tree (a & b)) (x: a)
  : Lemma (requires S.strictly_sorted c (keys t))
          (ensures contains c t x == (S.key_index c (keys t) x >= 0))
          [SMTPat (contains c t x); SMTPat (S.strictly_sorted c (keys t))]
  = find_keys c t x x

let rec leftmost_keys (#a #b: Type0) (t: T.tree (a & b)) (d: a)
  : Lemma (ensures leftmost t d == (if T.size t = 0 then d else Seq.index (keys t) 0))
          (decreases t)
          [SMTPat (leftmost t d)]
  = match t with
    | T.Leaf -> ()
    | T.Branch T.Leaf _ _ -> ()
    | T.Branch l (v, _) r -> leftmost_keys l d

let rec rightmost_keys (#a #b: Type0) (t: T.tree (a & b)) (d: a)
  : Lemma (ensures rightmost t d == (if T.size t = 0 then d else Seq.index (keys t) (T.size t - 1)))
          (decreases t)
          [SMTPat (rightmost t d)]
  = match t with
    | T.Leaf -> ()
    | T.Branch _ _ T.Leaf -> ()
    | T.Branch l (v, _) r -> rightmost_keys r d
