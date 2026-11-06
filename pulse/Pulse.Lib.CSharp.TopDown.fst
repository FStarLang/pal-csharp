module Pulse.Lib.CSharp.TopDown

/// R27.26. Top-down red-black insertion, as `SortedSet<T>.AddIfNotPresent` performs it,
/// over a boxed tree: a tree whose every node carries the box it lives in, its key and
/// whether it is red. The heap holds such a tree (`nodes`); this module is the pure half.
///
/// The insertion descends from the root, splitting every 4-node on the way and rotating
/// to repair the red parent a split can leave. `descent` is its loop invariant: the path
/// from the root to `current` is a valid 2-3-4 descent. `step` is one iteration, and
/// `insert_leaf` the final insertion; both are proved here without admits.

open Pulse.Lib.CSharp.Region
open Pulse.Lib.CSharp.RegionTree
open Pulse.Lib.CSharp.RegionPath
module B = Pulse.Lib.Box
module L = FStar.List.Tot
module T = Pulse.Lib.CSharp.Tree
module O = Pulse.Lib.CSharp.Order
module S = Pulse.Lib.CSharp.Sorted
module ST = Pulse.Lib.CSharp.SearchTree
module Seq = FStar.Seq

/// `c.Compare(k, v)` as the program reads it: only its sign (`Sorted.compare_i32`).
let cmp (#a: Type0) (c: O.comparer a) (k v: a) : int =
  if O.compare c k v < 0 then -1 else if O.compare c k v = 0 then 0 else 1

(* ------------------------------------------------------------------------------------ *)
(* Colour-tagged boxed trees                                                             *)

/// A boxed red-black tree: each node is `(box, (key, red))`.
let nt (r a: Type0) = T.tree (B.box r & (a & bool))
let fr (r a: Type0) = frame r (a & bool)

/// The tree without its boxes.
let rec strip (#r #e: Type0) (t: T.tree (B.box r & e)) : Tot (T.tree e) (decreases t) =
  match t with
  | T.Leaf -> T.Leaf
  | T.Branch l (_, v) rr -> T.Branch (strip l) v (strip rr)

let rec strip_bmap (#a #v: Type0) (view: B.box a -> a -> v) (t: T.tree (B.box a & a))
  : Lemma (ensures strip (bmap view t) == vmap view t) (decreases t)
          [SMTPat (strip (bmap view t))]
  = match t with T.Leaf -> () | T.Branch l _ rr -> strip_bmap view l; strip_bmap view rr

let nred (#r #a: Type0) (t: nt r a) : bool =
  match t with T.Leaf -> false | T.Branch _ (_, (_, red)) _ -> red

let nkey (#r #a: Type0) (t: nt r a) (d: a) : a =
  match t with T.Leaf -> d | T.Branch _ (_, (k, _)) _ -> k

let recolorn (#r #a: Type0) (t: nt r a) (red: bool) : nt r a =
  match t with T.Leaf -> T.Leaf | T.Branch l (b, (k, _)) rr -> T.Branch l (b, (k, red)) rr

/// `Node.Split4Node`: the root red, its children black.
let split4n (#r #a: Type0) (t: nt r a) : nt r a =
  match t with
  | T.Leaf -> T.Leaf
  | T.Branch l (b, (k, _)) rr -> T.Branch (recolorn l false) (b, (k, true)) (recolorn rr false)

/// `Node.Merge2Nodes`: the root black, its children red.
let merge2n (#r #a: Type0) (t: nt r a) : nt r a =
  match t with
  | T.Leaf -> T.Leaf
  | T.Branch l (b, (k, _)) rr -> T.Branch (recolorn l true) (b, (k, false)) (recolorn rr true)

let strip_nred (#r #a: Type0) (t: nt r a)
  : Lemma (ensures nred t == ST.is_red (strip t)) [SMTPat (nred t)]
  = ()

let strip_recolorn (#r #a: Type0) (t: nt r a) (red: bool)
  : Lemma (ensures strip (recolorn t red) == ST.recolor (strip t) red)
          [SMTPat (strip (recolorn t red))]
  = ()

let strip_split4n (#r #a: Type0) (t: nt r a)
  : Lemma (ensures strip (split4n t) == ST.split4 (strip t)) [SMTPat (strip (split4n t))]
  = ()

let strip_merge2n (#r #a: Type0) (t: nt r a)
  : Lemma (ensures strip (merge2n t) == ST.merge2 (strip t)) [SMTPat (strip (merge2n t))]
  = ()

let strip_rot_left (#r #e: Type0) (t: T.tree (B.box r & e))
  : Lemma (ensures strip (ST.rot_left t) == ST.rot_left (strip t)) [SMTPat (strip (ST.rot_left t))]
  = ()

let strip_rot_right (#r #e: Type0) (t: T.tree (B.box r & e))
  : Lemma (ensures strip (ST.rot_right t) == ST.rot_right (strip t)) [SMTPat (strip (ST.rot_right t))]
  = ()

let strip_rot_left_right (#r #e: Type0) (t: T.tree (B.box r & e))
  : Lemma (ensures strip (ST.rot_left_right t) == ST.rot_left_right (strip t))
          [SMTPat (strip (ST.rot_left_right t))]
  = match t with T.Branch l _ _ -> strip_rot_left l | _ -> ()

let strip_rot_right_left (#r #e: Type0) (t: T.tree (B.box r & e))
  : Lemma (ensures strip (ST.rot_right_left t) == ST.rot_right_left (strip t))
          [SMTPat (strip (ST.rot_right_left t))]
  = match t with T.Branch _ _ rr -> strip_rot_right rr | _ -> ()

let rec size_strip (#r #e: Type0) (t: T.tree (B.box r & e))
  : Lemma (ensures T.size (strip t) == T.size t) (decreases t) [SMTPat (T.size (strip t))]
  = match t with T.Leaf -> () | T.Branch l _ rr -> size_strip l; size_strip rr

(* ------------------------------------------------------------------------------------ *)
(* What a path leaves alone                                                              *)

let fkey (#r #a: Type0) (f: fr r a) : a = fst f.fval
let fred (#r #a: Type0) (f: fr r a) : bool = snd f.fval

/// The search for `k` took every frame of `fs`: no frame's key is equivalent to `k`, and the
/// path went right exactly where `k` is greater.
let rec on_path (#r #a: Type0) (c: O.comparer a) (k: a) (fs: list (fr r a)) : prop =
  match fs with
  | [] -> True
  | f :: rest ->
    O.compare c k (fkey f) <> 0 /\ f.went_right == (O.compare c k (fkey f) > 0) /\ on_path c k rest

let rec keys_plug (#r #a: Type0) (fs: list (fr r a)) (s s': nt r a)
  : Lemma (requires ST.keys (strip s) == ST.keys (strip s'))
          (ensures ST.keys (strip (plug fs s)) == ST.keys (strip (plug fs s')))
          (decreases fs)
  = match fs with [] -> () | f :: rest -> keys_plug rest (fill f s) (fill f s')

let rec contains_plug (#r #a: Type0) (c: O.comparer a) (k: a) (fs: list (fr r a)) (s: nt r a)
  : Lemma (requires on_path c k fs)
          (ensures ST.contains c (strip (plug fs s)) k == ST.contains c (strip s) k)
          (decreases fs)
  = match fs with [] -> () | f :: rest -> contains_plug c k rest (fill f s)

(* Red-black shape *)

/// A red frame's subtree is not red.
let joint_ok (#r #a: Type0) (fs: list (fr r a)) (s: nt r a) : bool =
  match fs with [] -> true | f :: _ -> not (fred f && nred s)

let rb_fill (#r #a: Type0) (f: fr r a) (s: nt r a)
  : Lemma (ensures ST.rb (strip (fill f s)) <==>
                   (ST.rb (strip f.fsib) /\ ST.rb (strip s) /\
                    ST.black_height (strip f.fsib) == ST.black_height (strip s) /\
                    not (fred f && (nred f.fsib || nred s))))
  = ()

let bh_fill (#r #a: Type0) (f: fr r a) (s: nt r a)
  : Lemma (requires ST.rb (strip (fill f s)))
          (ensures ST.black_height (strip (fill f s)) ==
                   ST.black_height (strip s) + (if fred f then 0 else 1))
  = ()

let rec rb_plug_sub (#r #a: Type0) (fs: list (fr r a)) (s: nt r a)
  : Lemma (requires ST.rb (strip (plug fs s)))
          (ensures ST.rb (strip s) /\ joint_ok fs s)
          (decreases fs)
  = match fs with
    | [] -> ()
    | f :: rest -> rb_plug_sub rest (fill f s); rb_fill f s

/// Replacing a subtree by one of the same black height that its parent's colour allows keeps
/// the tree red-black.
let rec rb_replace (#r #a: Type0) (fs: list (fr r a)) (s s': nt r a)
  : Lemma (requires ST.rb (strip (plug fs s)) /\ ST.rb (strip s') /\
                    ST.black_height (strip s') == ST.black_height (strip s) /\ joint_ok fs s')
          (ensures ST.rb (strip (plug fs s')))
          (decreases fs)
  = match fs with
    | [] -> ()
    | f :: rest ->
      rb_plug_sub rest (fill f s);
      rb_fill f s; rb_fill f s';
      bh_fill f s; bh_fill f s';
      rb_replace rest (fill f s) (fill f s')

(* Insertion at the end of a path *)

/// Binary-search-tree insertion of a red leaf, on the tree without boxes.
let rec bst_ins (#a: Type0) (c: O.comparer a) (t: T.tree (a & bool)) (k: a)
  : Tot (T.tree (a & bool)) (decreases t)
  = match t with
    | T.Leaf -> T.Branch T.Leaf (k, true) T.Leaf
    | T.Branch l (v, g) rr ->
      let o = O.compare c k v in
      if o < 0 then T.Branch (bst_ins c l k) (v, g) rr
      else if o > 0 then T.Branch l (v, g) (bst_ins c rr k)
      else t

let rec ins_plug (#r #a: Type0) (c: O.comparer a) (k: a) (fs: list (fr r a)) (s s': nt r a)
  : Lemma (requires on_path c k fs /\ bst_ins c (strip s) k == strip s')
          (ensures bst_ins c (strip (plug fs s)) k == strip (plug fs s'))
          (decreases fs)
  = match fs with [] -> () | f :: rest -> ins_plug c k rest (fill f s) (fill f s')

/// `k` inserted into `s` at position `i`.
let seq_ins (#a: Type0) (s: Seq.seq a) (i: nat{i <= Seq.length s}) (k: a) : Seq.seq a =
  Seq.append (Seq.snoc (Seq.slice s 0 i) k) (Seq.slice s i (Seq.length s))

let seq_ins_index (#a: Type0) (s: Seq.seq a) (i: nat{i <= Seq.length s}) (k: a) (j: nat)
  : Lemma (ensures Seq.length (seq_ins s i k) == Seq.length s + 1 /\
                   (j < i ==> Seq.index (seq_ins s i k) j == Seq.index s j) /\
                   (j == i ==> Seq.index (seq_ins s i k) j == k) /\
                   (i < j /\ j <= Seq.length s ==> Seq.index (seq_ins s i k) j == Seq.index s (j - 1)))
  = ()

let seq_ins_append_left (#a: Type0) (s1 s2: Seq.seq a) (i: nat{i <= Seq.length s1}) (k: a)
  : Lemma (ensures seq_ins (Seq.append s1 s2) i k == Seq.append (seq_ins s1 i k) s2)
  = let u = seq_ins (Seq.append s1 s2) i k in
    let w = Seq.append (seq_ins s1 i k) s2 in
    let aux (j: nat{j < Seq.length u}) : Lemma (Seq.index u j == Seq.index w j)
      = seq_ins_index (Seq.append s1 s2) i k j;
        seq_ins_index s1 i k j in
    FStar.Classical.forall_intro aux;
    Seq.lemma_eq_intro u w

let seq_ins_append_right (#a: Type0) (s1 s2: Seq.seq a) (i: nat{i <= Seq.length s2}) (k: a)
  : Lemma (ensures seq_ins (Seq.append s1 s2) (Seq.length s1 + i) k == Seq.append s1 (seq_ins s2 i k))
  = let u = seq_ins (Seq.append s1 s2) (Seq.length s1 + i) k in
    let w = Seq.append s1 (seq_ins s2 i k) in
    let aux (j: nat{j < Seq.length u}) : Lemma (Seq.index u j == Seq.index w j)
      = seq_ins_index (Seq.append s1 s2) (Seq.length s1 + i) k j;
        if j >= Seq.length s1 then seq_ins_index s2 i k (j - Seq.length s1) in
    FStar.Classical.forall_intro aux;
    Seq.lemma_eq_intro u w

let seq_ins_cons (#a: Type0) (v: a) (s: Seq.seq a) (i: nat{i <= Seq.length s}) (k: a)
  : Lemma (ensures seq_ins (Seq.cons v s) (i + 1) k == Seq.cons v (seq_ins s i k))
  = let u = seq_ins (Seq.cons v s) (i + 1) k in
    let w = Seq.cons v (seq_ins s i k) in
    let aux (j: nat{j < Seq.length u}) : Lemma (Seq.index u j == Seq.index w j)
      = seq_ins_index (Seq.cons v s) (i + 1) k j;
        if j >= 1 then seq_ins_index s i k (j - 1) in
    FStar.Classical.forall_intro aux;
    Seq.lemma_eq_intro u w

let rec keys_bst_ins (#a: Type0) (c: O.comparer a) (t: T.tree (a & bool)) (k: a)
  : Lemma (requires S.strictly_sorted c (ST.keys t) /\ not (ST.contains c t k))
          (ensures ST.keys (bst_ins c t k) == seq_ins (ST.keys t) (S.lower_bound c (ST.keys t) k) k)
          (decreases t)
  = match t with
    | T.Leaf -> Seq.lemma_eq_intro (ST.keys (bst_ins c t k)) (seq_ins (ST.keys t) 0 k)
    | T.Branch l (v, g) rr ->
      let sl = ST.keys l in
      let sr = ST.keys rr in
      ST.sorted_pivot c sl v sr;
      ST.lower_bound_pivot c sl v sr k;
      let o = O.compare c k v in
      if o < 0 then begin
        keys_bst_ins c l k;
        seq_ins_append_left sl (Seq.cons v sr) (S.lower_bound c sl k) k
      end else begin
        keys_bst_ins c rr k;
        seq_ins_cons v sr (S.lower_bound c sr k) k;
        seq_ins_append_right sl (Seq.cons v sr) (1 + S.lower_bound c sr k) k
      end

/// On a strictly sorted sequence, everything before `lower_bound` is less than `k` and
/// everything from it on is not.
let rec lower_bound_split (#a: Type0) (c: O.comparer a) (s: Seq.seq a) (k: a) (i: nat{i < Seq.length s})
  : Lemma (requires S.strictly_sorted c s)
          (ensures (i < S.lower_bound c s k ==> O.compare c (Seq.index s i) k < 0) /\
                   (i >= S.lower_bound c s k ==> O.compare c (Seq.index s i) k >= 0))
          (decreases Seq.length s)
  = let hd = Seq.head s in
    let tl = Seq.tail s in
    assert (S.strictly_sorted c tl);
    if i = 0 then begin
      if O.compare c hd k < 0 then ()
      else begin
        // lower_bound of the tail is 0: every later element is greater than the head.
        let aux (j: nat) : Lemma (j < Seq.length tl ==> O.compare c (Seq.index tl j) k >= 0)
          = if j < Seq.length tl then begin
              assert (Seq.index tl j == Seq.index s (j + 1));
              assert (O.compare c hd (Seq.index tl j) < 0);
              if O.compare c (Seq.index tl j) k < 0 then O.compare_trans c hd (Seq.index tl j) k
            end in
        FStar.Classical.forall_intro aux;
        ST.lower_bound_all_above c tl k
      end
    end else begin
      lower_bound_split c tl k (i - 1);
      if O.compare c hd k < 0 then ()
      else begin
        let aux (j: nat) : Lemma (j < Seq.length tl ==> O.compare c (Seq.index tl j) k >= 0)
          = if j < Seq.length tl then begin
              assert (Seq.index tl j == Seq.index s (j + 1));
              assert (O.compare c hd (Seq.index tl j) < 0);
              if O.compare c (Seq.index tl j) k < 0 then O.compare_trans c hd (Seq.index tl j) k
            end in
        FStar.Classical.forall_intro aux;
        ST.lower_bound_all_above c tl k
      end
    end

/// Inserting an absent key at its lower bound keeps a sequence strictly sorted.
let sorted_seq_ins (#a: Type0) (c: O.comparer a) (s: Seq.seq a) (k: a)
  : Lemma (requires S.strictly_sorted c s /\ S.key_index c s k < 0)
          (ensures S.strictly_sorted c (seq_ins s (S.lower_bound c s k) k))
  = let lb = S.lower_bound c s k in
    let s' = seq_ins s lb k in
    FStar.Classical.forall_intro (seq_ins_index s lb k);
    FStar.Classical.forall_intro (FStar.Classical.move_requires (lower_bound_split c s k));
    let above (j: nat{j < Seq.length s}) : Lemma (requires lb <= j) (ensures O.compare c k (Seq.index s j) < 0)
      = O.compare_antisym c (Seq.index s j) k;
        if j = lb then ()
        else (O.compare_antisym c (Seq.index s lb) k;
              O.compare_trans c k (Seq.index s lb) (Seq.index s j)) in
    FStar.Classical.forall_intro (FStar.Classical.move_requires above);
    let aux (i j: nat) : Lemma (ensures i < j /\ j < Seq.length s' ==> O.compare c (Seq.index s' i) (Seq.index s' j) < 0)
      = if i < j && j < Seq.length s' then begin
          if j < lb then ()
          else if j = lb then ()
          else if i < lb then O.compare_trans c (Seq.index s i) k (Seq.index s (j - 1))
          else if i = lb then ()
          else ()
        end in
    FStar.Classical.forall_intro_2 aux

let blacken (#r #a: Type0) (t: nt r a)
  : Lemma (requires ST.rb (strip t))
          (ensures ST.red_black (strip (recolorn t false)) /\
                   ST.keys (strip (recolorn t false)) == ST.keys (strip t))
  = ()

(* ------------------------------------------------------------------------------------ *)
(* The descent                                                                           *)

let distinct_nbranch (#r #e: Type0) (l: T.tree (B.box r & e)) (b: B.box r) (v: e) (rr: T.tree (B.box r & e))
  : Lemma (ensures distinct (nboxes (T.Branch l (b, v) rr)) <==>
                   (~ (L.memP b (nboxes l)) /\ ~ (L.memP b (nboxes rr)) /\
                    distinct (nboxes l) /\ distinct (nboxes rr) /\ disjoint (nboxes l) (nboxes rr)))
          [SMTPat (distinct (nboxes (T.Branch l (b, v) rr)))]
  = ()

/// The box of the `i`-th frame of a path, innermost first, or `null`.
let rec fb (#r #a: Type0) (fs: list (fr r a)) (i: nat) : Tot (B.box r) (decreases fs) =
  match fs with
  | [] -> B.null
  | f :: rest -> if i = 0 then f.fbox else fb rest (i - 1)

/// A leaf (where a new node goes) or a node whose two children are red (a 4-node).
let splittable (#r #a: Type0) (s: nt r a) : bool =
  match s with T.Leaf -> true | T.Branch l _ rr -> nred l && nred rr

/// `Node.Is4Node`.
let is4 (#r #a: Type0) (s: nt r a) : bool = T.Branch? s && splittable s

/// The child the search for `k` continues to: `order < 0 ? Left : Right`.
let dchild (#r #a: Type0) (c: O.comparer a) (k: a) (s: nt r a) : nt r a =
  match s with
  | T.Leaf -> T.Leaf
  | T.Branch l (_, (v, _)) rr -> if O.compare c k v < 0 then l else rr

let all_nonnull (#r #e: Type0) (t: T.tree (B.box r & e)) : prop =
  forall (y: B.box r). L.memP y (nboxes t) ==> B.is_null y == false

/// A boxed tree that is a set of `k0`'s keys and red-black, but for a possibly red root.
let ok (#r #a: Type0) (c: O.comparer a) (k0: Seq.seq a) (n: nt r a) : prop =
  ST.keys (strip n) == k0 /\ S.strictly_sorted c k0 /\ ST.rb (strip n) /\
  distinct (nboxes n) /\ all_nonnull n

/// The descent invariant at the focus `(fs, s)`: `current` is `s`'s root (null at a leaf),
/// `parent` and `grandParent` are the first two frames, and `order` compared `k` with the
/// parent. Two facts carry the 2-3-4 shape:
/// * if the parent is red and `s` will be split (or is where the new node goes), there is a
///   grandparent, the parent's sibling is black, and `greatGrandParent` is right;
/// * if `s` is red and its next node will be split, `s`'s sibling is black.
let dinv (#r #a: Type0) (c: O.comparer a) (k: a) (fs: list (fr r a)) (s: nt r a)
    (cur par gp ggp: B.box r) (order: int) : prop =
  on_path c k fs /\ cur == top s /\ par == fb fs 0 /\ gp == fb fs 1 /\
  (match fs with
   | [] -> True
   | f0 :: rest ->
     order == cmp c k (fkey f0) /\
     (fred f0 /\ splittable s ==>
       (match rest with
        | f1 :: rest' -> nred f1.fsib == false /\ ggp == fb rest' 0
        | [] -> False))) /\
  (nred s /\ splittable (dchild c k s) ==>
    (match fs with f0 :: _ -> nred f0.fsib == false | [] -> False))

let descent (#r #a: Type0) (c: O.comparer a) (k: a) (n: nt r a) (cur par gp ggp: B.box r) (order: int)
  : prop =
  exists (w: list (fr r a) & nt r a). n == plug (fst w) (snd w) /\
                                    dinv c k (fst w) (snd w) cur par gp ggp order

let descent_intro (#r #a: Type0) (c: O.comparer a) (k: a) (fs: list (fr r a)) (s: nt r a)
    (cur par gp ggp: B.box r) (order: int)
  : Lemma (requires dinv c k fs s cur par gp ggp order)
          (ensures descent c k (plug fs s) cur par gp ggp order)
  = assert (plug fs s == plug (fst (fs, s)) (snd (fs, s)))

let descent_elim (#r #a: Type0) (c: O.comparer a) (k: a) (n: nt r a) (cur par gp ggp: B.box r)
    (order: int)
  : Ghost (list (fr r a) & nt r a)
          (requires descent c k n cur par gp ggp order)
          (ensures fun w -> n == plug (fst w) (snd w) /\ dinv c k (fst w) (snd w) cur par gp ggp order)
  = FStar.IndefiniteDescription.indefinite_description_ghost (list (fr r a) & nt r a)
      (fun w -> n == plug (fst w) (snd w) /\ dinv c k (fst w) (snd w) cur par gp ggp order)

/// Where the descent starts.
let descent_root (#r #a: Type0) (c: O.comparer a) (k: a) (n: nt r a)
  : Lemma (requires ST.red_black (strip n))
          (ensures descent c k n (top n) B.null B.null B.null 0)
  = descent_intro c k [] n (top n) B.null B.null B.null 0

(* ------------------------------------------------------------------------------------ *)
(* InsertionBalance                                                                      *)

/// The rotation `InsertionBalance` chooses at the grandparent, from the sides the path took
/// at the parent (`w0`) and at the grandparent (`w1`).
let rot_for (#r #e: Type0) (w0 w1: bool) (t: T.tree (B.box r & e)) : T.tree (B.box r & e) =
  if w0 = w1 then (if w0 then ST.rot_left t else ST.rot_right t)
  else (if w0 then ST.rot_left_right t else ST.rot_right_left t)

/// The grandparent's subtree after `InsertionBalance`: rotated, the old grandparent red and
/// the new top black.
let balance_sub (#r #a: Type0) (w0 w1: bool) (t: nt r a) : nt r a =
  let g = top t in
  let rt = rot_for w0 w1 t in
  recolorn (replace rt g (recolorn (sub rt g) true)) false

/// `InsertionBalance(current, …)` on the whole tree.
let balance (#r #a: Type0) (n: nt r a) (cur: B.box r) : nt r a =
  match fst (focus n cur) with
  | f0 :: f1 :: _ -> replace n f1.fbox (balance_sub f0.went_right f1.went_right (sub n f1.fbox))
  | _ -> n

/// Whether `InsertionBalance` does a single rotation (the parent stays `current`'s parent).
let same_side (#r #a: Type0) (n: nt r a) (cur: B.box r) : bool =
  match fst (focus n cur) with
  | f0 :: f1 :: _ -> f0.went_right = f1.went_right
  | _ -> true

/// What `InsertionBalance(current, parent, grandParent, greatGrandParent)` requires.
let balance_ready (#r #a: Type0) (n: nt r a) (cur par gp ggp: B.box r) : prop =
  distinct (nboxes n) /\ all_nonnull n /\ L.memP cur (nboxes n) /\
  (match fst (focus n cur) with
   | f0 :: f1 :: rest -> f0.fbox == par /\ f1.fbox == gp /\ fb rest 0 == ggp
   | _ -> False)

/// The parent of `x`: the box of the first frame of its focus, or null.
let parent_of (#r #e: Type0) (n: T.tree (B.box r & e)) (x: B.box r) : B.box r =
  match fst (focus n x) with f :: _ -> f.fbox | [] -> B.null

/// `t`'s boxes avoid the path from the root to `x`.
let fits (#r #e: Type0) (n: T.tree (B.box r & e)) (x: B.box r) (t: T.tree (B.box r & e)) : prop =
  disjoint (fboxes (fst (focus n x))) (nboxes t)

/// The subtree at `p` with one child replaced.
let set_child (#r #e: Type0) (n: T.tree (B.box r & e)) (p: B.box r) (right: bool)
    (u: T.tree (B.box r & e)) : T.tree (B.box r & e) =
  replace n p (match sub n p with
               | T.Leaf -> T.Leaf
               | T.Branch l v rr -> if right then T.Branch l v u else T.Branch u v rr)

(* ------------------------------------------------------------------------------------ *)
(* Focus facts                                                                           *)

let nboxes_recolorn (#r #a: Type0) (t: nt r a) (red: bool)
  : Lemma (ensures nboxes (recolorn t red) == nboxes t) [SMTPat (nboxes (recolorn t red))]
  = ()

let nboxes_split4n (#r #a: Type0) (t: nt r a)
  : Lemma (ensures nboxes (split4n t) == nboxes t) [SMTPat (nboxes (split4n t))]
  = ()

let top_split4n (#r #a: Type0) (t: nt r a)
  : Lemma (ensures top (split4n t) == top t) [SMTPat (top (split4n t))]
  = ()

let rec focus_absent_acc (#r #e: Type0) (t: T.tree (B.box r & e)) (x: B.box r) (acc: list (frame r e))
  : Lemma (requires ~ (L.memP x (nboxes t))) (ensures T.Leaf? (snd (focus_acc t x acc))) (decreases t)
  = match t with
    | T.Leaf -> ()
    | T.Branch l (b, v) rr ->
      mem_box_nboxes x l;
      focus_absent_acc rr x ({ went_right = true; fbox = b; fval = v; fsib = l } :: acc)

/// A box the tree does not hold has an empty subtree.
let sub_absent (#r #e: Type0) (t: T.tree (B.box r & e)) (x: B.box r)
  : Lemma (requires ~ (L.memP x (nboxes t))) (ensures sub t x == T.Leaf)
  = focus_absent_acc t x []

let focus_at (#r #a: Type0) (fs: list (fr r a)) (s: nt r a)
  : Lemma (requires distinct (nboxes (plug fs s)) /\ T.Branch? s)
          (ensures focus (plug fs s) (top s) == (fs, s) /\ sub (plug fs s) (top s) == s /\
                   L.memP (top s) (nboxes (plug fs s)) /\
                   (forall (u: nt r a). replace (plug fs s) (top s) u == plug fs u))
  = focus_unique fs s

(* ------------------------------------------------------------------------------------ *)
(* The balanced subtree                                                                  *)

/// What `balance` leaves at the grandparent, for a red node `s` under a red parent (frame
/// `f0`) under a black grandparent (frame `f1`).
let bal_result (#r #a: Type0) (f0 f1: fr r a) (s: nt r a) : nt r a =
  match s with
  | T.Leaf -> T.Leaf
  | T.Branch sa (sc, (sk, _)) sb ->
    let p = f0.fbox in
    let g = f1.fbox in
    let kp = fkey f0 in
    let kg = fkey f1 in
    let psib = f0.fsib in
    let u = f1.fsib in
    match f0.went_right, f1.went_right with
    | false, false -> T.Branch s (p, (kp, false)) (T.Branch psib (g, (kg, true)) u)
    | true, true -> T.Branch (T.Branch u (g, (kg, true)) psib) (p, (kp, false)) s
    | true, false ->
      T.Branch (T.Branch psib (p, f0.fval) sa) (sc, (sk, false)) (T.Branch sb (g, (kg, true)) u)
    | false, true ->
      T.Branch (T.Branch u (g, (kg, true)) sa) (sc, (sk, false)) (T.Branch sb (p, f0.fval) psib)

#push-options "--fuel 4 --ifuel 2 --z3rlimit 40"
let balance_sub_shape (#r #a: Type0) (f0 f1: fr r a) (s: nt r a)
  : Lemma (requires distinct (nboxes (fill f1 (fill f0 s))) /\ T.Branch? s)
          (ensures balance_sub f0.went_right f1.went_right (fill f1 (fill f0 s)) == bal_result f0 f1 s)
  = let T.Branch sa (sc, (sk, sr)) sb = s in
    let g = f1.fbox in
    let t = fill f1 (fill f0 s) in
    let rt = rot_for f0.went_right f1.went_right t in
    mem_box_nboxes g f0.fsib; mem_box_nboxes g s; mem_box_nboxes g sa; mem_box_nboxes g sb;
    mem_box_nboxes g f1.fsib; mem_box_nboxes g (fill f0 s);
    match f0.went_right, f1.went_right with
    | false, false ->
      let fp = { went_right = true; fbox = f0.fbox; fval = f0.fval; fsib = s } in
      assert (rt == fill fp (T.Branch f0.fsib (g, f1.fval) f1.fsib));
      assert (focus rt g == ([fp], T.Branch f0.fsib (g, f1.fval) f1.fsib))
    | true, true ->
      let fp = { went_right = false; fbox = f0.fbox; fval = f0.fval; fsib = s } in
      mem_box_nboxes g (T.Branch f1.fsib (g, f1.fval) f0.fsib);
      assert (rt == fill fp (T.Branch f1.fsib (g, f1.fval) f0.fsib));
      assert (focus rt g == ([fp], T.Branch f1.fsib (g, f1.fval) f0.fsib))
    | true, false ->
      let left = T.Branch f0.fsib (f0.fbox, f0.fval) sa in
      mem_box_nboxes g left;
      assert (focus rt g == ([{ went_right = true; fbox = sc; fval = (sk, sr); fsib = left }],
                             T.Branch sb (g, f1.fval) f1.fsib))
    | false, true ->
      let left = T.Branch f1.fsib (g, f1.fval) sa in
      assert (focus rt g == ([{ went_right = false; fbox = sc; fval = (sk, sr);
                                fsib = T.Branch sb (f0.fbox, f0.fval) f0.fsib }], left))
#pop-options

let balance_shape (#r #a: Type0) (f0 f1: fr r a) (rest: list (fr r a)) (s: nt r a)
  : Lemma (requires distinct (nboxes (plug (f0 :: f1 :: rest) s)) /\ T.Branch? s)
          (ensures balance (plug (f0 :: f1 :: rest) s) (top s) == plug rest (bal_result f0 f1 s) /\
                   same_side (plug (f0 :: f1 :: rest) s) (top s) == (f0.went_right = f1.went_right))
  = focus_at (f0 :: f1 :: rest) s;
    let gt = fill f1 (fill f0 s) in
    distinct_plug rest gt;
    focus_at rest gt;
    balance_sub_shape f0 f1 s

/// A non-red node whose children are not both red: the descent passes it without a split
/// and without leaving a red-red pair.
let firm (#r #a: Type0) (t: nt r a) : bool =
  T.Branch? t && not (nred t) && not (splittable t)

#push-options "--fuel 3 --ifuel 2 --z3rlimit 100"
let bal_rb (#r #a: Type0) (f0 f1: fr r a) (s0 s: nt r a)
  : Lemma (requires ST.rb (strip (fill f1 (fill f0 s0))) /\ fred f0 /\ nred f1.fsib == false /\
                    T.Branch? s /\ nred s /\ ST.rb (strip s) /\
                    ST.black_height (strip s) == ST.black_height (strip s0))
          (ensures (let t = bal_result f0 f1 s in
                    ST.rb (strip t) /\ nred t == false /\
                    ST.black_height (strip t) == ST.black_height (strip (fill f1 (fill f0 s0)))))
  = rb_fill f1 (fill f0 s0); rb_fill f0 s0
#pop-options

#push-options "--fuel 2 --ifuel 2 --z3rlimit 100"
let bal_keys (#r #a: Type0) (f0 f1: fr r a) (s: nt r a)
  : Lemma (requires T.Branch? s)
          (ensures ST.keys (strip (bal_result f0 f1 s)) == ST.keys (strip (fill f1 (fill f0 s))))
  = let T.Branch sa (_, (sk, _)) sb = s in
    let ks x = ST.keys (strip x) in
    let c1 (v: a) = Seq.create 1 v in
    let kp = c1 (fkey f0) in
    let kg = c1 (fkey f1) in
    let kc = c1 sk in
    let ps = ks f0.fsib in
    let u = ks f1.fsib in
    let a_ = ks sa in
    let b_ = ks sb in
    let k_s = ks s in
    let sq = Seq.append in
    match f0.went_right, f1.went_right with
    | false, false ->
      Seq.append_assoc k_s kp ps; Seq.append_assoc (sq k_s kp) ps (sq kg u);
      Seq.append_assoc ps kg u; Seq.append_assoc k_s kp (sq ps (sq kg u));
      Seq.append_assoc kp ps (sq kg u)
    | true, true ->
      Seq.append_assoc u kg ps; Seq.append_assoc (sq u kg) ps (sq kp k_s);
      Seq.append_assoc u kg (sq ps (sq kp k_s)); Seq.append_assoc kg ps (sq kp k_s)
    | true, false ->
      Seq.lemma_eq_intro (ST.keys (strip (bal_result f0 f1 s))) (ST.keys (strip (fill f1 (fill f0 s))))
    | false, true ->
      Seq.lemma_eq_intro (ST.keys (strip (bal_result f0 f1 s))) (ST.keys (strip (fill f1 (fill f0 s))))

let bal_boxes (#r #a: Type0) (f0 f1: fr r a) (s: nt r a)
  : Lemma (requires T.Branch? s)
          (ensures (let t = bal_result f0 f1 s in
                    let t0 = fill f1 (fill f0 s) in
                    (forall (y: B.box r). L.memP y (nboxes t) <==> L.memP y (nboxes t0)) /\
                    (distinct (nboxes t0) ==> distinct (nboxes t)) /\
                    top t0 == f1.fbox))
  = ()
#pop-options

(* ------------------------------------------------------------------------------------ *)
(* One iteration                                                                         *)

/// The child the search for `k` leaves behind.
let osib (#r #a: Type0) (c: O.comparer a) (k: a) (s: nt r a) : nt r a =
  match s with
  | T.Leaf -> T.Leaf
  | T.Branch l (_, (v, _)) rr -> if O.compare c k v < 0 then rr else l

/// The next `current`: the root of the child the search continues to.
let next (#r #a: Type0) (c: O.comparer a) (k: a) (n: nt r a) (cur: B.box r) : B.box r =
  top (dchild c k (sub n cur))

/// Moving down from `s`: `current` becomes `s`'s child, `parent` `s`, `grandParent` the old
/// parent, and `greatGrandParent` `g` (which only matters if `s` is red).
#push-options "--fuel 2 --ifuel 2 --z3rlimit 40"
let push (#r #a: Type0) (c: O.comparer a) (k: a) (fs: list (fr r a)) (s: nt r a)
    (par g: B.box r) (o: int)
  : Lemma (requires on_path c k fs /\ T.Branch? s /\ par == fb fs 0 /\
                    o == cmp c k (nkey s k) /\ o <> 0 /\
                    (nred s /\ splittable (dchild c k s) ==>
                      (match fs with f0 :: rest -> nred f0.fsib == false /\ g == fb rest 0
                                   | [] -> False)) /\
                    (nred (dchild c k s) /\ splittable (dchild c k (dchild c k s)) ==>
                      nred (osib c k s) == false))
          (ensures descent c k (plug fs s) (top (dchild c k s)) (top s) par g o)
  = let T.Branch l (b, v) rr = s in
    let f = { went_right = o > 0; fbox = b; fval = v; fsib = osib c k s } in
    assert (fill f (dchild c k s) == s);
    descent_intro c k (f :: fs) (dchild c k s) (top (dchild c k s)) (top s) par g o
#pop-options

let ok_focus (#r #a: Type0) (c: O.comparer a) (k0: Seq.seq a) (fs: list (fr r a)) (s: nt r a)
  : Lemma (requires ok c k0 (plug fs s) /\ T.Branch? s)
          (ensures focus (plug fs s) (top s) == (fs, s) /\ sub (plug fs s) (top s) == s /\
                   L.memP (top s) (nboxes (plug fs s)) /\ B.is_null (top s) == false /\
                   ST.rb (strip s) /\ joint_ok fs s /\
                   (forall (u: nt r a). replace (plug fs s) (top s) u == plug fs u))
  = focus_at fs s; rb_plug_sub fs s

/// The parent's subtree, as `IsNonNullRed(parent)` sees it.
let sub_par (#r #a: Type0) (fs: list (fr r a)) (s: nt r a)
  : Lemma (requires distinct (nboxes (plug fs s)) /\ all_nonnull (plug fs s))
          (ensures nred (sub (plug fs s) (fb fs 0)) ==
                   (match fs with f0 :: _ -> fred f0 | [] -> false))
  = match fs with
    | [] -> sub_absent s B.null
    | f0 :: rest -> focus_at rest (fill f0 s)

#push-options "--fuel 3 --ifuel 2 --z3rlimit 60"
let split_facts (#r #a: Type0) (c: O.comparer a) (k: a) (s: nt r a)
  : Lemma (requires is4 s /\ ST.rb (strip s))
          (ensures (let s1 = split4n s in
                    T.Branch? s1 /\ nred s1 /\ ST.rb (strip s1) /\
                    ST.black_height (strip s1) == ST.black_height (strip s) /\
                    ST.keys (strip s1) == ST.keys (strip s) /\
                    top s1 == top s /\ nkey s1 k == nkey s k /\
                    (forall (y: B.box r). L.memP y (nboxes s1) <==> L.memP y (nboxes s)) /\
                    (match s1 with
                     | T.Branch sa _ sb -> firm sa /\ firm sb
                     | _ -> False) /\
                    firm (dchild c k s1)))
  = ()
#pop-options

/// No split: move down.
let step_plain (#r #a: Type0) (c: O.comparer a) (k0: Seq.seq a) (k: a) (n: nt r a)
    (cur par gp ggp: B.box r) (o0 o: int)
  : Lemma (requires ok c k0 n /\ descent c k n cur par gp ggp o0 /\ B.is_null cur == false /\
                    o == cmp c k (nkey (sub n cur) k) /\ o <> 0 /\ not (is4 (sub n cur)))
          (ensures descent c k n (next c k n cur) cur par gp o)
  = let (fs, s) = descent_elim c k n cur par gp ggp o0 in
    ok_focus c k0 fs s;
    push c k fs s par gp o

/// A split under a black parent (or at the root).
#push-options "--fuel 2 --ifuel 2 --z3rlimit 60"
let step_split_black (#r #a: Type0) (c: O.comparer a) (k0: Seq.seq a) (k: a)
    (fs: list (fr r a)) (s: nt r a) (gp: B.box r) (o: int)
  : Lemma (requires ok c k0 (plug fs s) /\ on_path c k fs /\ is4 s /\
                    o == cmp c k (nkey s k) /\ o <> 0 /\ gp == fb fs 1 /\
                    (match fs with f0 :: _ -> fred f0 == false | [] -> True))
          (ensures (let n1 = plug fs (split4n s) in
                    ok c k0 n1 /\ sub n1 (top s) == split4n s /\
                    descent c k n1 (next c k n1 (top s)) (top s) (fb fs 0) gp o))
  = ok_focus c k0 fs s;
    split_facts c k s;
    let s1 = split4n s in
    rb_replace fs s s1;
    keys_plug fs s s1;
    focus_at fs s1;
    push c k fs s1 (fb fs 0) gp o
#pop-options

let bal_frame (#r #a: Type0) (f0 f1: fr r a) : fr r a =
  { went_right = f0.went_right; fbox = f0.fbox; fval = (fkey f0, false);
    fsib = if f0.went_right then T.Branch f1.fsib (f1.fbox, (fkey f1, true)) f0.fsib
           else T.Branch f0.fsib (f1.fbox, (fkey f1, true)) f1.fsib }

/// A red node `s1` (just split, or just inserted) under a red parent: `InsertionBalance`.
#push-options "--fuel 2 --ifuel 2 --z3rlimit 100"
let step_balance (#r #a: Type0) (c: O.comparer a) (k0: Seq.seq a) (k: a)
    (f0 f1: fr r a) (rest: list (fr r a)) (s s1: nt r a)
  : Lemma (requires ST.rb (strip (plug (f0 :: f1 :: rest) s)) /\ fred f0 /\ nred f1.fsib == false /\
                    T.Branch? s1 /\ nred s1 /\ ST.rb (strip s1) /\
                    ST.black_height (strip s1) == ST.black_height (strip s) /\
                    distinct (nboxes (plug (f0 :: f1 :: rest) s1)) /\
                    all_nonnull (plug (f0 :: f1 :: rest) s1) /\
                    ST.keys (strip (plug (f0 :: f1 :: rest) s1)) == k0 /\ S.strictly_sorted c k0)
          (ensures (let n1 = plug (f0 :: f1 :: rest) s1 in
                    let n2 = plug rest (bal_result f0 f1 s1) in
                    distinct (nboxes n1) /\ all_nonnull n1 /\
                    focus n1 (top s1) == (f0 :: f1 :: rest, s1) /\
                    balance n1 (top s1) == n2 /\
                    same_side n1 (top s1) == (f0.went_right = f1.went_right) /\
                    ok c k0 n2))
  = let n = plug (f0 :: f1 :: rest) s in
    let t0 = fill f1 (fill f0 s) in
    let t1 = fill f1 (fill f0 s1) in
    rb_plug_sub rest t0;
    assert (distinct (nboxes t1));
    focus_at (f0 :: f1 :: rest) s1;
    balance_shape f0 f1 rest s1;
    bal_rb f0 f1 s s1;
    bal_keys f0 f1 s1;
    bal_boxes f0 f1 s1;
    rb_replace rest t0 (bal_result f0 f1 s1);
    keys_plug rest t1 (bal_result f0 f1 s1)
#pop-options

/// After `InsertionBalance` at a split node, the descent goes on from it.
#push-options "--fuel 2 --ifuel 2 --z3rlimit 100"
let step_balance_descent (#r #a: Type0) (c: O.comparer a) (k: a)
    (f0 f1: fr r a) (rest: list (fr r a)) (s1: nt r a) (gp: B.box r) (o: int)
  : Lemma (requires on_path c k (f0 :: f1 :: rest) /\ nred s1 /\
                    (match s1 with T.Branch sa _ sb -> firm sa /\ firm sb | _ -> False) /\
                    distinct (nboxes (plug rest (bal_result f0 f1 s1))) /\
                    o == cmp c k (nkey s1 k) /\ o <> 0)
          (ensures (let n2 = plug rest (bal_result f0 f1 s1) in
                    let par2 = if f0.went_right = f1.went_right then f0.fbox else fb rest 0 in
                    descent c k n2 (next c k n2 (top s1)) (top s1) par2 gp o))
  = let t = bal_result f0 f1 s1 in
    if f0.went_right = f1.went_right then begin
      let fp = bal_frame f0 f1 in
      assert (fill fp s1 == t);
      assert (plug rest t == plug (fp :: rest) s1);
      focus_at (fp :: rest) s1;
      push c k (fp :: rest) s1 f0.fbox gp o
    end else begin
      focus_at rest t;
      push c k rest t (fb rest 0) gp o
    end
#pop-options

/// A split: `current.Split4Node()`, then `InsertionBalance` if the parent is red.
#push-options "--fuel 2 --ifuel 2 --z3rlimit 60"
let step_split (#r #a: Type0) (c: O.comparer a) (k0: Seq.seq a) (k: a) (n: nt r a)
    (cur par gp ggp: B.box r) (o0 o: int)
  : Lemma (requires ok c k0 n /\ descent c k n cur par gp ggp o0 /\ B.is_null cur == false /\
                    o == cmp c k (nkey (sub n cur) k) /\ o <> 0 /\ is4 (sub n cur))
          (ensures (let n1 = replace n cur (split4n (sub n cur)) in
                    (nred (sub n1 par) == false ==>
                      ok c k0 n1 /\ descent c k n1 (next c k n1 cur) cur par gp o) /\
                    (nred (sub n1 par) ==>
                      balance_ready n1 cur par gp ggp /\
                      (let n2 = balance n1 cur in
                       let par2 = if same_side n1 cur then par else ggp in
                       ok c k0 n2 /\ descent c k n2 (next c k n2 cur) cur par2 gp o))))
  = let (fs, s) = descent_elim c k n cur par gp ggp o0 in
    ok_focus c k0 fs s;
    split_facts c k s;
    let s1 = split4n s in
    let n1 = plug fs s1 in
    assert (replace n cur s1 == n1);
    assert (distinct (nboxes n1));
    keys_plug fs s s1;
    sub_par fs s1;
    match fs with
    | [] -> step_split_black c k0 k fs s gp o
    | f0 :: rest ->
      if fred f0 then begin
        let f1 :: rest' = rest in
        assert (splittable s);
        assert (ggp == fb rest' 0 /\ nred f1.fsib == false);
        step_balance c k0 k f0 f1 rest' s s1;
        step_balance_descent c k f0 f1 rest' s1 gp o;
        assert (L.memP cur (nboxes n1));
        assert (fst (focus n1 cur) == f0 :: f1 :: rest');
        assert (f0.fbox == par /\ f1.fbox == gp);
        assert (balance_ready n1 cur par gp ggp);
        assert (same_side n1 cur == (f0.went_right = f1.went_right));
        assert (nred (sub n1 par))
      end else step_split_black c k0 k fs s gp o
#pop-options

(* ------------------------------------------------------------------------------------ *)
(* Termination                                                                           *)

/// R27.26. The insertion loop's measure, at the subtree `s` of `current`. A node's 2-3-4
/// level is its black height, one more for a red node (it belongs to its parent's 2-3-4
/// node); within a level, a black 4-node (about to be split) ranks above any other black
/// node, which ranks above a red node whose next node is a 4-node, which ranks above any
/// other red node. A split may move `current` up a level (`InsertionBalance`'s double
/// rotation), but only to a red node whose next node is not a 4-node.
let meas (#r #a: Type0) (c: O.comparer a) (k: a) (s: nt r a) : nat =
  match s with
  | T.Leaf -> 0
  | T.Branch _ _ _ ->
    let h = ST.black_height (strip s) in
    if nred s then (if is4 (dchild c k s) then 4 * h + 5 else 4 * h + 3)
    else (if is4 s then 4 * h + 4 else 4 * h + 2)

/// The subtree at the root of the subtree at the end of a path.
let sub_top (#r #a: Type0) (fs: list (fr r a)) (s: nt r a)
  : Lemma (requires distinct (nboxes (plug fs s)) /\ all_nonnull (plug fs s))
          (ensures sub (plug fs s) (top s) == s)
  = match s with
    | T.Branch _ _ _ -> focus_at fs s
    | T.Leaf -> sub_absent (plug fs s) (B.null #r)

#push-options "--fuel 2 --ifuel 2 --z3rlimit 40"
/// Moving down from a node that is not split.
let meas_child (#r #a: Type0) (c: O.comparer a) (k: a) (s: nt r a)
  : Lemma (requires T.Branch? s /\ ST.rb (strip s) /\ not (is4 s))
          (ensures meas c k (dchild c k s) < meas c k s)
  = ()

/// Moving down from a 4-node just split.
let meas_split (#r #a: Type0) (c: O.comparer a) (k: a) (s: nt r a)
  : Lemma (requires is4 s /\ ST.rb (strip s))
          (ensures meas c k (dchild c k (split4n s)) + 2 == meas c k s)
  = ()
#pop-options

/// The step that does not split.
#push-options "--fuel 2 --ifuel 2 --z3rlimit 40"
let meas_plain (#r #a: Type0) (c: O.comparer a) (k0: Seq.seq a) (k: a) (n: nt r a)
    (cur par gp ggp: B.box r) (o0 o: int)
  : Lemma (requires ok c k0 n /\ descent c k n cur par gp ggp o0 /\ B.is_null cur == false /\
                    o == cmp c k (nkey (sub n cur) k) /\ o <> 0 /\ not (is4 (sub n cur)))
          (ensures meas c k (sub n (next c k n cur)) < meas c k (sub n cur))
  = let (fs, s) = descent_elim c k n cur par gp ggp o0 in
    ok_focus c k0 fs s;
    let T.Branch l (b, v) rr = s in
    let f = { went_right = o > 0; fbox = b; fval = v; fsib = osib c k s } in
    assert (fill f (dchild c k s) == s);
    assert (plug (f :: fs) (dchild c k s) == n);
    sub_top (f :: fs) (dchild c k s);
    meas_child c k s
#pop-options

/// The red node `InsertionBalance`'s double rotation leaves `current` at: its next node is
/// a child of the split node, which is not a 4-node.
#push-options "--fuel 3 --ifuel 2 --z3rlimit 100"
let meas_bal (#r #a: Type0) (c: O.comparer a) (k: a) (f0 f1: fr r a) (s1: nt r a)
  : Lemma (requires on_path c k [f0; f1] /\ nred s1 /\
                    (match s1 with T.Branch sa _ sb -> firm sa /\ firm sb | _ -> False) /\
                    ST.rb (strip (bal_result f0 f1 s1)) /\ fred f0 /\
                    O.compare c k (nkey s1 k) <> 0)
          (ensures (let t = bal_result f0 f1 s1 in
                    let y = if f0.went_right = f1.went_right then dchild c k s1 else dchild c k t in
                    meas c k y < 4 * ST.black_height (strip s1) + 4))
  = let T.Branch sa (sc, (sk, _)) sb = s1 in
    let t = bal_result f0 f1 s1 in
    let bh (x: nt r a) = ST.black_height (strip x) in
    match f0.went_right, f1.went_right with
    | false, false | true, true ->
      assert (ST.rb (strip s1));
      assert (bh sa == bh sb /\ bh s1 == bh sa)
    | true, false ->
      let T.Branch y1 _ y2 = t in
      assert (ST.rb (strip y1) /\ ST.rb (strip y2) /\ bh y1 == bh y2);
      assert (bh y1 == bh sa /\ bh y2 == bh sb /\ bh s1 == bh sa);
      assert (dchild c k y1 == sa /\ dchild c k y2 == sb)
    | false, true ->
      let T.Branch y1 _ y2 = t in
      assert (ST.rb (strip y1) /\ ST.rb (strip y2) /\ bh y1 == bh y2);
      assert (bh y1 == bh sa /\ bh y2 == bh sb /\ bh s1 == bh sa);
      assert (dchild c k y1 == sa /\ dchild c k y2 == sb)
#pop-options

let on_path2 (#r #a: Type0) (c: O.comparer a) (k: a) (f0 f1: fr r a) (rest: list (fr r a))
  : Lemma (requires on_path c k (f0 :: f1 :: rest)) (ensures on_path c k [f0; f1])
  = assert_norm (on_path c k [f0; f1] <==>
                 (O.compare c k (fkey f0) <> 0 /\ f0.went_right == (O.compare c k (fkey f0) > 0) /\
                  (O.compare c k (fkey f1) <> 0 /\ f1.went_right == (O.compare c k (fkey f1) > 0) /\ True)))

/// The split under a red parent, then `InsertionBalance`.
#push-options "--fuel 2 --ifuel 2 --z3rlimit 100"
let meas_balanced (#r #a: Type0) (c: O.comparer a) (k0: Seq.seq a) (k: a)
    (f0 f1: fr r a) (rest: list (fr r a)) (s: nt r a) (o: int)
  : Lemma (requires ok c k0 (plug (f0 :: f1 :: rest) s) /\ on_path c k (f0 :: f1 :: rest) /\
                    is4 s /\ fred f0 /\ nred f1.fsib == false /\
                    o == cmp c k (nkey s k) /\ o <> 0)
          (ensures (let s1 = split4n s in
                    let n2 = plug rest (bal_result f0 f1 s1) in
                    meas c k (sub n2 (top (dchild c k (sub n2 (top s))))) < meas c k s))
  = let n = plug (f0 :: f1 :: rest) s in
    ok_focus c k0 (f0 :: f1 :: rest) s;
    split_facts c k s;
    meas_split c k s;
    let s1 = split4n s in
    keys_plug (f0 :: f1 :: rest) s s1;
    step_balance c k0 k f0 f1 rest s s1;
    let t = bal_result f0 f1 s1 in
    let n2 = plug rest t in
    rb_plug_sub rest t;
    on_path2 c k f0 f1 rest;
    meas_bal c k f0 f1 s1;
    let T.Branch _ (b, v) _ = s1 in
    if f0.went_right = f1.went_right then begin
      let fp = bal_frame f0 f1 in
      let f = { went_right = o > 0; fbox = b; fval = v; fsib = osib c k s1 } in
      assert (fill f (dchild c k s1) == s1);
      assert (fill fp s1 == t);
      assert (plug (fp :: rest) s1 == n2);
      focus_at (fp :: rest) s1;
      sub_top (f :: fp :: rest) (dchild c k s1)
    end else begin
      let T.Branch tl (tb, tv) tr = t in
      let ft = { went_right = o > 0; fbox = tb; fval = tv; fsib = osib c k t } in
      assert (fill ft (dchild c k t) == t);
      focus_at rest t;
      sub_top (ft :: rest) (dchild c k t)
    end
#pop-options

#push-options "--fuel 2 --ifuel 2 --z3rlimit 100"
/// The step that splits; when the parent is red, after `InsertionBalance`.
let meas_step_split (#r #a: Type0) (c: O.comparer a) (k0: Seq.seq a) (k: a) (n: nt r a)
    (cur par gp ggp: B.box r) (o0 o: int)
  : Lemma (requires ok c k0 n /\ descent c k n cur par gp ggp o0 /\ B.is_null cur == false /\
                    o == cmp c k (nkey (sub n cur) k) /\ o <> 0 /\ is4 (sub n cur))
          (ensures (let n1 = replace n cur (split4n (sub n cur)) in
                    (nred (sub n1 par) == false ==>
                      meas c k (sub n1 (next c k n1 cur)) < meas c k (sub n cur)) /\
                    (nred (sub n1 par) ==>
                      (let n2 = balance n1 cur in
                       meas c k (sub n2 (next c k n2 cur)) < meas c k (sub n cur)))))
  = step_split c k0 k n cur par gp ggp o0 o;
    let (fs, s) = descent_elim c k n cur par gp ggp o0 in
    ok_focus c k0 fs s;
    split_facts c k s;
    meas_split c k s;
    let s1 = split4n s in
    let n1 = plug fs s1 in
    assert (replace n cur s1 == n1);
    let T.Branch l (b, v) rr = s1 in
    let f = { went_right = o > 0; fbox = b; fval = v; fsib = osib c k s1 } in
    assert (fill f (dchild c k s1) == s1);
    sub_par fs s1;
    match fs with
    | [] -> focus_at fs s1; sub_top (f :: fs) (dchild c k s1)
    | f0 :: rest ->
      if fred f0 then begin
        let f1 :: rest' = rest in
        assert (splittable s);
        assert (nred f1.fsib == false);
        meas_balanced c k0 k f0 f1 rest' s o;
        balance_shape f0 f1 rest' s1
      end else begin
        focus_at fs s1;
        sub_top (f :: fs) (dchild c k s1)
      end
#pop-options

/// A descent whose parent is a node: the parent is in the tree, `order` compared `k` with
/// its key, and the next node of the parent is `current`.
#push-options "--fuel 2 --ifuel 2 --z3rlimit 40"
let descent_next (#r #a: Type0) (c: O.comparer a) (k0: Seq.seq a) (k: a) (n: nt r a)
    (x cur gp ggp: B.box r) (o: int)
  : Lemma (requires ok c k0 n /\ descent c k n x cur gp ggp o /\ B.is_null cur == false)
          (ensures L.memP cur (nboxes n) /\ o == cmp c k (nkey (sub n cur) k) /\ o <> 0 /\
                   next c k n cur == x)
  = let (fs, s) = descent_elim c k n x cur gp ggp o in
    let f0 :: rest = fs in
    let t = fill f0 s in
    assert (plug rest t == n);
    focus_at rest t
#pop-options

(* ------------------------------------------------------------------------------------ *)
(* The end of the descent                                                                *)

/// `order == 0`: the key is already there.
let found (#r #a: Type0) (c: O.comparer a) (k0: Seq.seq a) (k: a) (n: nt r a)
    (cur par gp ggp: B.box r) (o0: int)
  : Lemma (requires ok c k0 n /\ descent c k n cur par gp ggp o0 /\ B.is_null cur == false /\
                    O.compare c k (nkey (sub n cur) k) == 0)
          (ensures S.key_index c k0 k >= 0)
  = let (fs, s) = descent_elim c k n cur par gp ggp o0 in
    ok_focus c k0 fs s;
    contains_plug c k fs s

/// The new red node.
let leaf (#r #a: Type0) (x: B.box r) (k: a) : nt r a = T.Branch T.Leaf (x, (k, true)) T.Leaf

/// `current == null`: the new node goes where the search ended, as `parent`'s child on the
/// side `order` says; `InsertionBalance` follows if `parent` is red.
#push-options "--fuel 2 --ifuel 2 --z3rlimit 100"
let insert_leaf (#r #a: Type0) (c: O.comparer a) (k0: Seq.seq a) (k: a) (n: nt r a)
    (par gp ggp: B.box r) (o: int) (x: B.box r)
  : Lemma (requires ok c k0 n /\ descent c k n B.null par gp ggp o /\ T.Branch? n /\
                    B.is_null x == false /\ ~ (L.memP x (nboxes n)))
          (ensures S.key_index c k0 k < 0 /\
                   (let n1 = set_child n par (o > 0) (leaf x k) in
                    let k1 = seq_ins k0 (S.lower_bound c k0 k) k in
                    (nred (sub n1 par) == false ==> ok c k1 n1) /\
                    (nred (sub n1 par) ==> balance_ready n1 x par gp ggp /\ ok c k1 (balance n1 x))))
  = let (fs, s) = descent_elim c k n B.null par gp ggp o in
    (match s with
     | T.Branch _ _ _ -> ok_focus c k0 fs s; assert (B.is_null #r B.null)
     | T.Leaf -> ());
    assert (s == T.Leaf);
    let f0 :: rest = fs in
    let lx = leaf x k in
    focus_at rest (fill f0 s);
    assert (sub n par == fill f0 s);
    let n1 = plug fs lx in
    assert (set_child n par (o > 0) lx == n1);
    contains_plug c k fs s;
    ins_plug c k fs s lx;
    keys_bst_ins c (strip n) k;
    sorted_seq_ins c k0 k;
    let k1 = seq_ins k0 (S.lower_bound c k0 k) k in
    distinct_plug fs s;
    distinct_plug fs lx;
    assert (~ (L.memP x (fboxes fs)));
    assert (distinct (nboxes n1));
    assert (all_nonnull n1);
    sub_par fs lx;
    rb_plug_sub fs s;
    assert_norm (ST.black_height (strip (leaf x k)) == 0 /\ ST.rb (strip (leaf x k)));
    if fred f0 then begin
      let f1 :: rest' = rest in
      step_balance c k1 k f0 f1 rest' T.Leaf lx;
      assert (balance_ready n1 x par gp ggp)
    end else
      rb_replace fs s lx
#pop-options

/// The end of `AddIfNotPresent`: `root.ColorBlack()`.
let finish (#r #a: Type0) (c: O.comparer a) (k0: Seq.seq a) (n: nt r a)
  : Lemma (requires ok c k0 n)
          (ensures ok c k0 (recolorn n false) /\ ST.red_black (strip (recolorn n false)))
  = ()
