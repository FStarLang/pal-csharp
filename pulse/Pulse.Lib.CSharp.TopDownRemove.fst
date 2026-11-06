module Pulse.Lib.CSharp.TopDownRemove

/// R27.30. Top-down red-black removal, as `SortedSet<T>.DoRemove` performs it, over the boxed
/// trees of `TopDown`: the pure half.
///
/// The removal descends from the root along the search for `k` (and, once `k` is found, on
/// to its successor), making every node it reaches not a 2-node: the root is turned red, a
/// red sibling is rotated up, two 2-node siblings are merged, and a 2-node next to a 3- or
/// 4-node borrows from it by a rotation. `rinv` is the loop invariant: the path from the root
/// to `current` is that search, `match`/`parentOfMatch` are where it met `k`, and the node
/// above `current` is not a 2-node. At the end the matching node is replaced by its
/// successor (`rdel`). Everything is proved here without admits.

open Pulse.Lib.CSharp.Region
open Pulse.Lib.CSharp.RegionTree
open Pulse.Lib.CSharp.RegionPath
open Pulse.Lib.CSharp.TopDown
module B = Pulse.Lib.Box
module L = FStar.List.Tot
module T = Pulse.Lib.CSharp.Tree
module O = Pulse.Lib.CSharp.Order
module S = Pulse.Lib.CSharp.Sorted
module ST = Pulse.Lib.CSharp.SearchTree
module Seq = FStar.Seq

(* ------------------------------------------------------------------------------------ *)
(* The search                                                                            *)

/// The path is the search for `k`, going right at a key equivalent to `k`: the search for
/// the place just after `k`, which is where `DoRemove` goes on to after the match.
let rec on_rpath (#r #a: Type0) (c: O.comparer a) (k: a) (fs: list (fr r a)) : prop =
  match fs with
  | [] -> True
  | f :: rest -> f.went_right == (O.compare c k (fkey f) >= 0) /\ on_rpath c k rest

/// The innermost frame whose key is equivalent to `k`, and the box of the frame above it.
let rec mfind (#r #a: Type0) (c: O.comparer a) (k: a) (fs: list (fr r a))
  : Tot (option (B.box r & B.box r)) (decreases fs)
  = match fs with
    | [] -> None
    | f :: rest -> if O.compare c k (fkey f) = 0 then Some (f.fbox, fb rest 0) else mfind c k rest

/// `foundMatch`, `match` and `parentOfMatch` as the path has them.
let mstate (#r #a: Type0) (c: O.comparer a) (k: a) (fs: list (fr r a)) (mt pom: B.box r)
    (found: bool) : prop =
  found == Some? (mfind c k fs) /\
  (match mfind c k fs with
   | Some (m, pm) -> mt == m /\ pom == pm
   | None -> B.is_null mt)

/// `Node.Is2Node`: a black node with no red child.
let is2 (#r #a: Type0) (s: nt r a) : bool =
  match s with
  | T.Leaf -> false
  | T.Branch l (_, (_, red)) rr -> not red && not (nred l) && not (nred rr)

/// The node above `current` is not a 2-node: it, `current` or `current`'s sibling is red.
let lc (#r #a: Type0) (fs: list (fr r a)) (s: nt r a) : bool =
  match fs with
  | [] -> true
  | f0 :: _ -> fred f0 || nred s || nred f0.fsib

/// The loop invariant at the focus `(fs, s)`, at the top of an iteration.
let rinv (#r #a: Type0) (c: O.comparer a) (k: a) (fs: list (fr r a)) (s: nt r a)
    (cur par gp mt pom: B.box r) (found: bool) : prop =
  on_rpath c k fs /\ cur == top s /\ par == fb fs 0 /\ gp == fb fs 1 /\
  mstate c k fs mt pom found /\ lc fs s

/// After the fix-up of a 2-node `current` under a non-null parent, before the merge or the
/// rotation: the parent is red, `current` a 2-node, and its sibling a black node.
let rmid (#r #a: Type0) (c: O.comparer a) (k: a) (fs: list (fr r a)) (s: nt r a)
    (cur par gp mt pom: B.box r) (found: bool) : prop =
  on_rpath c k fs /\ cur == top s /\ par == fb fs 0 /\ gp == fb fs 1 /\
  mstate c k fs mt pom found /\ is2 s /\
  (match fs with
   | f0 :: _ -> fred f0 /\ nred f0.fsib == false /\ T.Branch? f0.fsib
   | [] -> False)

/// After the fix-up: `current` is not a 2-node.
let rfx (#r #a: Type0) (c: O.comparer a) (k: a) (fs: list (fr r a)) (s: nt r a)
    (cur par mt pom: B.box r) (found: bool) : prop =
  on_rpath c k fs /\ cur == top s /\ par == fb fs 0 /\
  mstate c k fs mt pom found /\ T.Branch? s /\ not (is2 s)

let rdesc (#r #a: Type0) (c: O.comparer a) (k: a) (n: nt r a) (cur par gp mt pom: B.box r)
    (found: bool) : prop =
  exists (w: list (fr r a) & nt r a). n == plug (fst w) (snd w) /\
                                    rinv c k (fst w) (snd w) cur par gp mt pom found

let rdesc_intro (#r #a: Type0) (c: O.comparer a) (k: a) (fs: list (fr r a)) (s: nt r a)
    (cur par gp mt pom: B.box r) (found: bool)
  : Lemma (requires rinv c k fs s cur par gp mt pom found)
          (ensures rdesc c k (plug fs s) cur par gp mt pom found)
  = assert (plug fs s == plug (fst (fs, s)) (snd (fs, s)))

let rdesc_elim (#r #a: Type0) (c: O.comparer a) (k: a) (n: nt r a) (cur par gp mt pom: B.box r)
    (found: bool)
  : Ghost (list (fr r a) & nt r a)
          (requires rdesc c k n cur par gp mt pom found)
          (ensures fun w -> n == plug (fst w) (snd w) /\ rinv c k (fst w) (snd w) cur par gp mt pom found)
  = FStar.IndefiniteDescription.indefinite_description_ghost (list (fr r a) & nt r a)
      (fun w -> n == plug (fst w) (snd w) /\ rinv c k (fst w) (snd w) cur par gp mt pom found)

let mdesc (#r #a: Type0) (c: O.comparer a) (k: a) (n: nt r a) (cur par gp mt pom: B.box r)
    (found: bool) : prop =
  exists (w: list (fr r a) & nt r a). n == plug (fst w) (snd w) /\
                                    rmid c k (fst w) (snd w) cur par gp mt pom found

let mdesc_intro (#r #a: Type0) (c: O.comparer a) (k: a) (fs: list (fr r a)) (s: nt r a)
    (cur par gp mt pom: B.box r) (found: bool)
  : Lemma (requires rmid c k fs s cur par gp mt pom found)
          (ensures mdesc c k (plug fs s) cur par gp mt pom found)
  = assert (plug fs s == plug (fst (fs, s)) (snd (fs, s)))

let mdesc_elim (#r #a: Type0) (c: O.comparer a) (k: a) (n: nt r a) (cur par gp mt pom: B.box r)
    (found: bool)
  : Ghost (list (fr r a) & nt r a)
          (requires mdesc c k n cur par gp mt pom found)
          (ensures fun w -> n == plug (fst w) (snd w) /\ rmid c k (fst w) (snd w) cur par gp mt pom found)
  = FStar.IndefiniteDescription.indefinite_description_ghost (list (fr r a) & nt r a)
      (fun w -> n == plug (fst w) (snd w) /\ rmid c k (fst w) (snd w) cur par gp mt pom found)

let fdesc (#r #a: Type0) (c: O.comparer a) (k: a) (n: nt r a) (cur par mt pom: B.box r)
    (found: bool) : prop =
  exists (w: list (fr r a) & nt r a). n == plug (fst w) (snd w) /\
                                    rfx c k (fst w) (snd w) cur par mt pom found

let fdesc_intro (#r #a: Type0) (c: O.comparer a) (k: a) (fs: list (fr r a)) (s: nt r a)
    (cur par mt pom: B.box r) (found: bool)
  : Lemma (requires rfx c k fs s cur par mt pom found)
          (ensures fdesc c k (plug fs s) cur par mt pom found)
  = assert (plug fs s == plug (fst (fs, s)) (snd (fs, s)))

let fdesc_elim (#r #a: Type0) (c: O.comparer a) (k: a) (n: nt r a) (cur par mt pom: B.box r)
    (found: bool)
  : Ghost (list (fr r a) & nt r a)
          (requires fdesc c k n cur par mt pom found)
          (ensures fun w -> n == plug (fst w) (snd w) /\ rfx c k (fst w) (snd w) cur par mt pom found)
  = FStar.IndefiniteDescription.indefinite_description_ghost (list (fr r a) & nt r a)
      (fun w -> n == plug (fst w) (snd w) /\ rfx c k (fst w) (snd w) cur par mt pom found)

(* ------------------------------------------------------------------------------------ *)
(* Order along a path                                                                    *)

let rec sorted_plug_sub (#r #a: Type0) (c: O.comparer a) (fs: list (fr r a)) (s: nt r a)
  : Lemma (requires S.strictly_sorted c (ST.keys (strip (plug fs s))))
          (ensures S.strictly_sorted c (ST.keys (strip s)))
          (decreases fs)
  = match fs with
    | [] -> ()
    | f :: rest ->
      sorted_plug_sub c rest (fill f s);
      let T.Branch l (_, (v, g)) rr = fill f s in
      ST.sorted_branch c (strip l) v g (strip rr)

let above_pivot (#a: Type0) (c: O.comparer a) (k: a) (sl: Seq.seq a) (v: a) (sr: Seq.seq a)
  : Lemma (requires ST.above_all c k (Seq.append sl (Seq.cons v sr)))
          (ensures ST.above_all c k sl /\ O.compare c k v < 0 /\ ST.above_all c k sr)
  = FStar.Classical.forall_intro (ST.index_pivot sl v sr);
    assert (Seq.index (Seq.append sl (Seq.cons v sr)) (Seq.length sl) == v);
    assert (forall (i: nat). i < Seq.length sr ==>
              Seq.index (Seq.append sl (Seq.cons v sr)) (Seq.length sl + 1 + i) == Seq.index sr i)

/// Everything at the end of a path is above `k` if everything is.
let rec above_plug_sub (#r #a: Type0) (c: O.comparer a) (k: a) (fs: list (fr r a)) (s: nt r a)
  : Lemma (requires ST.above_all c k (ST.keys (strip (plug fs s))))
          (ensures ST.above_all c k (ST.keys (strip s)) /\
                   (match fs with f :: _ -> O.compare c k (fkey f) < 0 | [] -> True))
          (decreases fs)
  = match fs with
    | [] -> ()
    | f :: rest ->
      above_plug_sub c k rest (fill f s);
      let T.Branch l (_, (v, _)) rr = fill f s in
      above_pivot c k (ST.keys (strip l)) v (ST.keys (strip rr))

/// Past the match, everything is above `k`.
let rec found_above (#r #a: Type0) (c: O.comparer a) (k: a) (fs: list (fr r a)) (s: nt r a)
  : Lemma (requires on_rpath c k fs /\ S.strictly_sorted c (ST.keys (strip (plug fs s))) /\
                    Some? (mfind c k fs))
          (ensures ST.above_all c k (ST.keys (strip s)))
          (decreases fs)
  = match fs with
    | f :: rest ->
      if O.compare c k (fkey f) = 0 then begin
        sorted_plug_sub c rest (fill f s);
        ST.sorted_branch c (strip f.fsib) (fkey f) (fred f) (strip s);
        let ks = ST.keys (strip s) in
        let aux (i: nat) : Lemma (i < Seq.length ks ==> O.compare c k (Seq.index ks i) < 0)
          = if i < Seq.length ks then O.compare_trans c k (fkey f) (Seq.index ks i) in
        FStar.Classical.forall_intro aux
      end else begin
        found_above c k rest (fill f s);
        above_plug_sub c k [f] s
      end

/// With no match, the path is the search for `k`.
let rec on_path_of (#r #a: Type0) (c: O.comparer a) (k: a) (fs: list (fr r a))
  : Lemma (requires on_rpath c k fs /\ None? (mfind c k fs)) (ensures on_path c k fs)
          (decreases fs)
  = match fs with [] -> () | _ :: rest -> on_path_of c k rest

(* ------------------------------------------------------------------------------------ *)
(* Sequences                                                                             *)

let rec plug_append (#r #e: Type0) (gs hs: list (frame r e)) (s: T.tree (B.box r & e))
  : Lemma (ensures plug (L.append gs hs) s == plug hs (plug gs s)) (decreases gs)
  = match gs with [] -> () | g :: rest -> plug_append rest hs (fill g s)

/// `k0` with its element at `i` removed.
let seq_del (#a: Type0) (s: Seq.seq a) (i: nat{i < Seq.length s}) : Seq.seq a =
  Seq.append (Seq.slice s 0 i) (Seq.slice s (i + 1) (Seq.length s))

/// The keys after removing `k`: `k0` without the element equivalent to `k`, if any.
let removed (#a: Type0) (c: O.comparer a) (k0: Seq.seq a) (k: a) : Seq.seq a =
  let i = S.key_index c k0 k in
  if i >= 0 then seq_del k0 i else k0

/// Removing a pivot.
let seq_del_pivot (#a: Type0) (sa: Seq.seq a) (x: a) (sb: Seq.seq a)
  : Lemma (ensures seq_del (Seq.append sa (Seq.cons x sb)) (Seq.length sa) == Seq.append sa sb)
  = let s = Seq.append sa (Seq.cons x sb) in
    FStar.Classical.forall_intro (ST.index_pivot sa x sb);
    Seq.lemma_eq_intro (seq_del s (Seq.length sa)) (Seq.append sa sb)

/// A pivot equivalent to `k` in a strictly sorted sequence is where `k` is.
let key_index_pivot (#a: Type0) (c: O.comparer a) (sa: Seq.seq a) (x: a) (sb: Seq.seq a) (k: a)
  : Lemma (requires S.strictly_sorted c (Seq.append sa (Seq.cons x sb)) /\ O.compare c k x == 0)
          (ensures S.key_index c (Seq.append sa (Seq.cons x sb)) k == Seq.length sa /\
                   removed c (Seq.append sa (Seq.cons x sb)) k == Seq.append sa sb)
  = let s = Seq.append sa (Seq.cons x sb) in
    let n = Seq.length sa in
    FStar.Classical.forall_intro (ST.index_pivot sa x sb);
    let lo (j: nat) : Lemma (j < n ==> O.compare c (Seq.index s j) k < 0)
      = if j < n then begin
          assert (Seq.index s n == x);
          assert (O.compare c (Seq.index s j) (Seq.index s n) < 0);
          O.compare_trans c (Seq.index s j) x k
        end in
    let hi (j: nat) : Lemma (n <= j /\ j < Seq.length s ==> O.compare c (Seq.index s j) k >= 0)
      = if n < j && j < Seq.length s then begin
          assert (Seq.index s n == x);
          assert (O.compare c (Seq.index s n) (Seq.index s j) < 0);
          O.compare_trans c k x (Seq.index s j)
        end in
    FStar.Classical.forall_intro lo;
    FStar.Classical.forall_intro hi;
    S.lower_bound_prefix c s k n;
    seq_del_pivot sa x sb

/// A pivot removed below the end of a path is a pivot removed from the whole tree.
let rec keys_del_plug (#r #a: Type0) (fs: list (fr r a)) (s s': nt r a) (sa: Seq.seq a) (x: a)
    (sb: Seq.seq a)
  : Ghost (Seq.seq a & Seq.seq a)
          (requires ST.keys (strip s) == Seq.append sa (Seq.cons x sb) /\
                    ST.keys (strip s') == Seq.append sa sb)
          (ensures fun (pa, pb) ->
             ST.keys (strip (plug fs s)) == Seq.append pa (Seq.cons x pb) /\
             ST.keys (strip (plug fs s')) == Seq.append pa pb)
          (decreases fs)
  = match fs with
    | [] -> (sa, sb)
    | f :: rest ->
      let ks = ST.keys (strip f.fsib) in
      let v = fkey f in
      if f.went_right then begin
        let sa' = Seq.append ks (Seq.cons v sa) in
        Seq.append_assoc ks (Seq.cons v sa) (Seq.cons x sb);
        Seq.lemma_eq_intro (Seq.append ks (Seq.cons v (Seq.append sa (Seq.cons x sb))))
                           (Seq.append sa' (Seq.cons x sb));
        Seq.lemma_eq_intro (Seq.append ks (Seq.cons v (Seq.append sa sb))) (Seq.append sa' sb);
        keys_del_plug rest (fill f s) (fill f s') sa' x sb
      end else begin
        let sb' = Seq.append sb (Seq.cons v ks) in
        Seq.lemma_eq_intro (Seq.append (Seq.append sa (Seq.cons x sb)) (Seq.cons v ks))
                           (Seq.append sa (Seq.cons x sb'));
        Seq.lemma_eq_intro (Seq.append (Seq.append sa sb) (Seq.cons v ks)) (Seq.append sa sb');
        keys_del_plug rest (fill f s) (fill f s') sa x sb'
      end

/// Down a path that only goes left, the first key is the first key of its end.
let rec all_left (#r #e: Type0) (fs: list (frame r e)) : bool =
  match fs with [] -> true | f :: rest -> not f.went_right && all_left rest

let rec keys_left_plug (#r #a: Type0) (fs: list (fr r a)) (s s': nt r a) (x: a)
  : Lemma (requires all_left fs /\ ST.keys (strip s) == Seq.cons x (ST.keys (strip s')))
          (ensures ST.keys (strip (plug fs s)) == Seq.cons x (ST.keys (strip (plug fs s'))))
          (decreases fs)
  = match fs with
    | [] -> ()
    | f :: rest ->
      let ks = ST.keys (strip f.fsib) in
      Seq.lemma_eq_intro (Seq.append (Seq.cons x (ST.keys (strip s'))) (Seq.cons (fkey f) ks))
                         (Seq.cons x (Seq.append (ST.keys (strip s')) (Seq.cons (fkey f) ks)));
      keys_left_plug rest (fill f s) (fill f s') x

/// A path past the match only goes left.
let rec left_past (#r #a: Type0) (c: O.comparer a) (k: a) (fs: list (fr r a)) (s: nt r a)
  : Lemma (requires on_rpath c k fs /\ ST.above_all c k (ST.keys (strip (plug fs s))))
          (ensures all_left fs)
          (decreases fs)
  = match fs with
    | [] -> ()
    | f :: rest ->
      above_plug_sub c k rest (fill f s);
      above_plug_sub c k [f] s;
      left_past c k rest (fill f s)

(* ------------------------------------------------------------------------------------ *)
(* Black height along a path                                                             *)

let rec bh_plug (#r #a: Type0) (fs: list (fr r a)) (s s': nt r a)
  : Lemma (requires ST.rb (strip (plug fs s)) /\ ST.rb (strip (plug fs s')) /\
                    ST.black_height (strip s) == ST.black_height (strip s'))
          (ensures ST.black_height (strip (plug fs s)) == ST.black_height (strip (plug fs s')))
          (decreases fs)
  = match fs with
    | [] -> ()
    | f :: rest ->
      rb_plug_sub rest (fill f s); rb_plug_sub rest (fill f s');
      bh_fill f s; bh_fill f s';
      bh_plug rest (fill f s) (fill f s')

(* ------------------------------------------------------------------------------------ *)
(* Re-shaping the subtree at a path's end                                                *)

/// Recolouring the node at `z`.
let rcol (#r #a: Type0) (t: nt r a) (z: B.box r) (red: bool) : nt r a =
  replace t z (recolorn (sub t z) red)

let rcol_plug (#r #a: Type0) (fs: list (fr r a)) (s: nt r a) (red: bool)
  : Lemma (requires distinct (nboxes (plug fs s)) /\ T.Branch? s)
          (ensures rcol (plug fs s) (top s) red == plug fs (recolorn s red))
  = focus_at fs s

/// A subtree swapped for one of the same boxes keeps the tree's boxes distinct and non-null.
let swap_boxes (#r #a: Type0) (fs: list (fr r a)) (t t': nt r a)
  : Lemma (requires distinct (nboxes (plug fs t)) /\ all_nonnull (plug fs t) /\ distinct (nboxes t') /\
                    (forall (y: B.box r). L.memP y (nboxes t') <==> L.memP y (nboxes t)))
          (ensures distinct (nboxes (plug fs t')) /\ all_nonnull (plug fs t') /\
                   (forall (y: B.box r). L.memP y (nboxes (plug fs t')) <==> L.memP y (nboxes (plug fs t))))
  = ()

/// The match is a box of the path.
let rec mfind_mem (#r #a: Type0) (c: O.comparer a) (k: a) (fs: list (fr r a))
  : Lemma (ensures (match mfind c k fs with Some (m, _) -> L.memP m (fboxes fs) | None -> True))
          (decreases fs)
  = match fs with [] -> () | _ :: rest -> mfind_mem c k rest

/// Whether the frame at a path's head is the match, by box.
let mstate_head (#r #a: Type0) (c: O.comparer a) (k: a) (f0: fr r a) (rest: list (fr r a))
    (s: nt r a) (mt pom: B.box r) (found: bool)
  : Lemma (requires mstate c k (f0 :: rest) mt pom found /\ distinct (nboxes (plug (f0 :: rest) s)) /\
                    B.is_null f0.fbox == false)
          (ensures eq_box f0.fbox mt == (O.compare c k (fkey f0) = 0))
  = mfind_mem c k rest;
    distinct_plug rest (fill f0 s);
    assert (~ (L.memP f0.fbox (fboxes rest)))

/// Every key of `t` is above `k`, or every one below.
let keys_above (#a: Type0) (c: O.comparer a) (k v: a) (ks: Seq.seq a)
  : Lemma (requires O.compare c k v < 0 /\ ST.above_all c v ks) (ensures ST.above_all c k ks)
  = let aux (i: nat) : Lemma (i < Seq.length ks ==> O.compare c k (Seq.index ks i) < 0)
      = if i < Seq.length ks then O.compare_trans c k v (Seq.index ks i) in
    FStar.Classical.forall_intro aux

let keys_below (#a: Type0) (c: O.comparer a) (k v: a) (ks: Seq.seq a)
  : Lemma (requires O.compare c k v >= 0 /\ ST.below_all c ks v)
          (ensures forall (i: nat). i < Seq.length ks ==> O.compare c k (Seq.index ks i) > 0)
  = let aux (i: nat) : Lemma (i < Seq.length ks ==> O.compare c k (Seq.index ks i) > 0)
      = if i < Seq.length ks then O.compare_trans c (Seq.index ks i) v k in
    FStar.Classical.forall_intro aux

let below_pivot (#a: Type0) (c: O.comparer a) (k: a) (sl: Seq.seq a) (v: a) (sr: Seq.seq a)
  : Lemma (requires forall (i: nat). i < Seq.length (Seq.append sl (Seq.cons v sr)) ==>
                      O.compare c k (Seq.index (Seq.append sl (Seq.cons v sr)) i) > 0)
          (ensures (forall (i: nat). i < Seq.length sl ==> O.compare c k (Seq.index sl i) > 0) /\
                   O.compare c k v > 0 /\
                   (forall (i: nat). i < Seq.length sr ==> O.compare c k (Seq.index sr i) > 0))
  = FStar.Classical.forall_intro (ST.index_pivot sl v sr);
    assert (Seq.index (Seq.append sl (Seq.cons v sr)) (Seq.length sl) == v);
    assert (forall (i: nat). i < Seq.length sr ==>
              Seq.index (Seq.append sl (Seq.cons v sr)) (Seq.length sl + 1 + i) == Seq.index sr i)

/// The sibling of the path's end is all on the side the path did not take.
let sib_side (#r #a: Type0) (c: O.comparer a) (k: a) (f0: fr r a) (rest: list (fr r a)) (s: nt r a)
  : Lemma (requires on_rpath c k (f0 :: rest) /\ S.strictly_sorted c (ST.keys (strip (plug (f0 :: rest) s))))
          (ensures (let ks = ST.keys (strip f0.fsib) in
                    (f0.went_right == false ==> ST.above_all c k ks) /\
                    (f0.went_right ==> (forall (i: nat). i < Seq.length ks ==> O.compare c k (Seq.index ks i) > 0))))
  = sorted_plug_sub c rest (fill f0 s);
    ST.sorted_branch c (strip (if f0.went_right then f0.fsib else s)) (fkey f0) (fred f0)
                       (strip (if f0.went_right then s else f0.fsib));
    if f0.went_right then keys_below c k (fkey f0) (ST.keys (strip f0.fsib))
    else keys_above c k (fkey f0) (ST.keys (strip f0.fsib))

(* ------------------------------------------------------------------------------------ *)
(* Fixing up a 2-node: the root, and a node that is not one                              *)

/// `current.ColorRed()` at the root.
let fix_root (#r #a: Type0) (c: O.comparer a) (k0: Seq.seq a) (k: a) (s: nt r a)
    (cur par gp mt pom: B.box r) (found: bool)
  : Lemma (requires ok c k0 s /\ rinv c k [] s cur par gp mt pom found /\ is2 s)
          (ensures ok c k0 (recolorn s true) /\ fdesc c k (recolorn s true) cur par mt pom found /\
                   sub (recolorn s true) cur == recolorn s true /\ T.size (recolorn s true) == T.size s)
  = focus_at [] (recolorn s true);
    fdesc_intro c k [] (recolorn s true) cur par mt pom found

/// `current` is not a 2-node: nothing to fix.
let fix_not2 (#r #a: Type0) (c: O.comparer a) (k: a) (n: nt r a) (cur par gp mt pom: B.box r)
    (found: bool) (k0: Seq.seq a)
  : Lemma (requires ok c k0 n /\ rdesc c k n cur par gp mt pom found /\ B.is_null cur == false /\
                    not (is2 (sub n cur)))
          (ensures fdesc c k n cur par mt pom found)
  = let (fs, s) = rdesc_elim c k n cur par gp mt pom found in
    (match s with T.Leaf -> () | _ -> ok_focus c k0 fs s);
    fdesc_intro c k fs s cur par mt pom found

/// A 2-node under a parent whose other child is black: the parent is red.
let fix_direct (#r #a: Type0) (c: O.comparer a) (k0: Seq.seq a) (k: a) (f0: fr r a)
    (rest: list (fr r a)) (s: nt r a) (cur par gp mt pom: B.box r) (found: bool)
  : Lemma (requires ok c k0 (plug (f0 :: rest) s) /\ rinv c k (f0 :: rest) s cur par gp mt pom found /\
                    is2 s /\ nred f0.fsib == false)
          (ensures rmid c k (f0 :: rest) s cur par gp mt pom found)
  = rb_plug_sub rest (fill f0 s);
    rb_fill f0 s

(* ------------------------------------------------------------------------------------ *)
(* A red sibling: rotate it up                                                           *)

/// A black node is at least one black level high.
let bh_black (#r #a: Type0) (t: nt r a)
  : Lemma (requires T.Branch? t /\ nred t == false) (ensures ST.black_height (strip t) >= 1)
  = ()

/// A node of black height at least one is a node.
let bh_branch (#r #a: Type0) (t: nt r a)
  : Lemma (requires ST.black_height (strip t) >= 1) (ensures T.Branch? t)
  = ()

/// The rotation that lifts the sibling `parent.Right == sibling ? RotateLeft : RotateRight`.
let arot (#r #e: Type0) (w: bool) (t: T.tree (B.box r & e)) : T.tree (B.box r & e) =
  if w then ST.rot_right t else ST.rot_left t

/// The two frames above `current` once its red sibling is lifted: the parent, now red, and
/// above it the sibling, now black.
let a_frames (#r #a: Type0) (f0: fr r a) : fr r a & fr r a =
  match f0.fsib with
  | T.Branch ql (q, (qk, _)) qr ->
    if f0.went_right then
      ({ went_right = true; fbox = f0.fbox; fval = (fkey f0, true); fsib = qr },
       { went_right = true; fbox = q; fval = (qk, false); fsib = ql })
    else
      ({ went_right = false; fbox = f0.fbox; fval = (fkey f0, true); fsib = ql },
       { went_right = false; fbox = q; fval = (qk, false); fsib = qr })
  | T.Leaf -> (f0, f0)

/// `parentOfMatch` after the lift.
let pom_a (#r: Type0) (p mt q pom: B.box r) : B.box r = if eq_box p mt then q else pom

#push-options "--fuel 3 --ifuel 2 --z3rlimit 60"
/// The lifted subtree.
let fix_a_shape (#r #a: Type0) (f0: fr r a) (s: nt r a)
  : Lemma (requires distinct (nboxes (fill f0 s)) /\ T.Branch? f0.fsib)
          (ensures (let p = f0.fbox in
                    let t0 = fill f0 s in
                    let u1 = arot f0.went_right t0 in
                    let u3 = recolorn (rcol u1 p true) false in
                    let (f0', f1') = a_frames f0 in
                    L.memP p (nboxes u1) /\ top u1 == top f0.fsib /\
                    u3 == fill f1' (fill f0' s) /\ L.memP p (nboxes u3) /\
                    ST.keys (strip u3) == ST.keys (strip t0) /\
                    (forall (y: B.box r). L.memP y (nboxes u3) <==> L.memP y (nboxes t0))))
  = let p = f0.fbox in
    let T.Branch ql (q, (qk, qc)) qr = f0.fsib in
    let w = f0.went_right in
    let t0 = fill f0 s in
    let u1 = arot w t0 in
    let inner = T.Branch (if w then qr else s) (p, f0.fval) (if w then s else ql) in
    let ff = { went_right = w; fbox = q; fval = (qk, qc); fsib = (if w then ql else qr) } in
    assert (u1 == fill ff inner);
    assert (ST.keys (strip u1) == ST.keys (strip t0));
    focus_at [ff] inner;
    keys_plug [ff] inner (recolorn inner true)
#pop-options

let key_above (#r #a: Type0) (c: O.comparer a) (k: a) (t: nt r a)
  : Lemma (requires T.Branch? t /\ ST.above_all c k (ST.keys (strip t)))
          (ensures O.compare c k (nkey t k) < 0)
  = let T.Branch l _ rr = t in above_pivot c k (ST.keys (strip l)) (nkey t k) (ST.keys (strip rr))

let key_below (#r #a: Type0) (c: O.comparer a) (k: a) (t: nt r a)
  : Lemma (requires T.Branch? t /\
                    (forall (i: nat). i < Seq.length (ST.keys (strip t)) ==>
                       O.compare c k (Seq.index (ST.keys (strip t)) i) > 0))
          (ensures O.compare c k (nkey t k) > 0)
  = let T.Branch l _ rr = t in below_pivot c k (ST.keys (strip l)) (nkey t k) (ST.keys (strip rr))

/// The sibling's key is on the side the path did not take.
let sib_key (#r #a: Type0) (c: O.comparer a) (k: a) (f0: fr r a) (rest: list (fr r a)) (s: nt r a)
  : Lemma (requires on_rpath c k (f0 :: rest) /\ S.strictly_sorted c (ST.keys (strip (plug (f0 :: rest) s))) /\
                    T.Branch? f0.fsib)
          (ensures (if f0.went_right then O.compare c k (nkey f0.fsib k) > 0
                    else O.compare c k (nkey f0.fsib k) < 0))
  = sib_side c k f0 rest s;
    if f0.went_right then key_below c k f0.fsib else key_above c k f0.fsib

#push-options "--fuel 2 --ifuel 2 --z3rlimit 80"
let fix_a (#r #a: Type0) (c: O.comparer a) (k0: Seq.seq a) (k: a) (f0: fr r a)
    (rest: list (fr r a)) (s: nt r a) (cur par gp mt pom: B.box r) (found: bool)
  : Lemma (requires ok c k0 (plug (f0 :: rest) s) /\ rinv c k (f0 :: rest) s cur par gp mt pom found /\
                    is2 s /\ nred f0.fsib)
          (ensures (let p = f0.fbox in
                    let q = top f0.fsib in
                    let w = f0.went_right in
                    let t0 = fill f0 s in
                    let u1 = arot w t0 in
                    let u3 = recolorn (rcol u1 p true) false in
                    let (f0', f1') = a_frames f0 in
                    let fs' = f0' :: f1' :: rest in
                    T.Branch? f0.fsib /\ fred f0 == false /\
                    B.is_null q == false /\ L.memP p (nboxes u1) /\ top u1 == q /\
                    u3 == fill f1' (fill f0' s) /\ L.memP p (nboxes u3) /\
                    plug fs' s == plug rest u3 /\
                    ok c k0 (plug fs' s) /\
                    rmid c k fs' s cur par q mt (pom_a p mt q pom) found))
  = let p = f0.fbox in
    let T.Branch ql (q, (qk, _)) qr = f0.fsib in
    let t0 = fill f0 s in
    rb_plug_sub rest t0;
    rb_fill f0 s;
    bh_black s;
    bh_branch ql; bh_branch qr;
    distinct_plug rest t0;
    let (f0', f1') = a_frames f0 in
    fix_a_shape f0 s;
    let u3 = fill f1' (fill f0' s) in
    swap_boxes rest t0 u3;
    keys_plug rest t0 u3;
    rb_replace rest t0 u3;
    sorted_plug_sub c rest t0;
    sib_key c k f0 rest s;
    mfind_mem c k rest;
    mstate_head c k f0 rest s mt pom found;
    assert (~ (L.memP q (fboxes rest)));
    assert (~ (q == p))
#pop-options

(* ------------------------------------------------------------------------------------ *)
(* Two 2-nodes: merge                                                                    *)

/// The frame above `current` after `parent.Merge2Nodes()`.
let m_frame (#r #a: Type0) (f0: fr r a) : fr r a =
  { went_right = f0.went_right; fbox = f0.fbox; fval = (fkey f0, false); fsib = recolorn f0.fsib true }

#push-options "--fuel 3 --ifuel 2 --z3rlimit 60"
let fix_merge (#r #a: Type0) (c: O.comparer a) (k0: Seq.seq a) (k: a) (f0: fr r a)
    (rest: list (fr r a)) (s: nt r a) (cur par gp mt pom: B.box r) (found: bool)
  : Lemma (requires ok c k0 (plug (f0 :: rest) s) /\ rmid c k (f0 :: rest) s cur par gp mt pom found /\
                    is2 f0.fsib)
          (ensures (let t1 = merge2n (fill f0 s) in
                    let fs' = m_frame f0 :: rest in
                    t1 == fill (m_frame f0) (recolorn s true) /\
                    plug fs' (recolorn s true) == plug rest t1 /\
                    ok c k0 (plug fs' (recolorn s true)) /\
                    rfx c k fs' (recolorn s true) cur par mt pom found))
  = let t0 = fill f0 s in
    let t1 = merge2n t0 in
    rb_plug_sub rest t0;
    rb_fill f0 s;
    distinct_plug rest t0;
    swap_boxes rest t0 t1;
    keys_plug rest t0 t1;
    rb_replace rest t0 t1
#pop-options

(* ------------------------------------------------------------------------------------ *)
(* A 2-node next to a 3- or 4-node: borrow by a rotation                                 *)

/// `Node.Rotate(rotation)` on boxed trees.
let rotn (#r #a: Type0) (rot: ST.tree_rotation) (t: nt r a) : nt r a =
  match rot, t with
  | ST.RotRight, T.Branch (T.Branch ll lv lr) v rr ->
    ST.rot_right (T.Branch (T.Branch (recolorn ll false) lv lr) v rr)
  | ST.RotLeft, T.Branch l v (T.Branch rl rv rr) ->
    ST.rot_left (T.Branch l v (T.Branch rl rv (recolorn rr false)))
  | ST.RotLeftRight, _ -> ST.rot_left_right t
  | ST.RotRightLeft, _ -> ST.rot_right_left t
  | _, _ -> t

let strip_rotn (#r #a: Type0) (rot: ST.tree_rotation) (t: nt r a)
  : Lemma (ensures strip (rotn rot t) == ST.rotate rot (strip t)) [SMTPat (strip (rotn rot t))]
  = match rot, t with
    | ST.RotRight, T.Branch (T.Branch ll lv lr) v rr -> ()
    | ST.RotLeft, T.Branch l v (T.Branch rl rv rr) -> ()
    | _ -> ()

let nboxes_rotn (#r #a: Type0) (rot: ST.tree_rotation) (t: nt r a) (y: B.box r)
  : Lemma (ensures L.memP y (nboxes (rotn rot t)) <==> L.memP y (nboxes t))
  = match rot, t with
    | ST.RotRight, T.Branch (T.Branch ll lv lr) v rr -> ()
    | ST.RotLeft, T.Branch l v (T.Branch rl rv rr) -> ()
    | ST.RotLeftRight, T.Branch (T.Branch a_ av (T.Branch b_ bv c_)) v d_ -> ()
    | ST.RotRightLeft, T.Branch a_ av (T.Branch (T.Branch b_ bv c_) cv d_) -> ()
    | _ -> ()

/// `parent.GetRotation(current, sibling)`, from the side `current` is on.
let b2_rot (#r #a: Type0) (w: bool) (sib: nt r a) : ST.tree_rotation =
  if w then (if nred (T.left sib) then ST.RotRight else ST.RotLeftRight)
  else (if nred (T.left sib) then ST.RotRightLeft else ST.RotLeft)

/// The two frames above `current` after the rotation: the parent, now black, and above it the
/// new grandparent, red.
let b2_frames (#r #a: Type0) (f0: fr r a) : fr r a & fr r a =
  let p = f0.fbox in
  let pk = fkey f0 in
  match f0.fsib with
  | T.Branch ql (q, (qk, qc)) qr ->
    if f0.went_right then begin
      if nred ql then
        ({ went_right = true; fbox = p; fval = (pk, false); fsib = qr },
         { went_right = true; fbox = q; fval = (qk, true); fsib = recolorn ql false })
      else (match qr with
            | T.Branch xl (x, (xk, _)) xr ->
              ({ went_right = true; fbox = p; fval = (pk, false); fsib = xr },
               { went_right = true; fbox = x; fval = (xk, true); fsib = T.Branch ql (q, (qk, qc)) xl })
            | T.Leaf -> (f0, f0))
    end else begin
      if nred ql then
        (match ql with
         | T.Branch xl (x, (xk, _)) xr ->
           ({ went_right = false; fbox = p; fval = (pk, false); fsib = xl },
            { went_right = false; fbox = x; fval = (xk, true); fsib = T.Branch xr (q, (qk, qc)) qr })
         | T.Leaf -> (f0, f0))
      else
        ({ went_right = false; fbox = p; fval = (pk, false); fsib = ql },
         { went_right = false; fbox = q; fval = (qk, true); fsib = recolorn qr false })
    end
  | T.Leaf -> (f0, f0)

/// Whether the sibling can lend: a black node with a red child.
let lends (#r #a: Type0) (sib: nt r a) : bool =
  match sib with
  | T.Branch ql (_, (_, qc)) qr -> not qc && (nred ql || nred qr)
  | T.Leaf -> false

#push-options "--fuel 4 --ifuel 2 --z3rlimit 100"
/// The rotated subtree, through the four writes `DoRemove` does to it.
let b2_shape (#r #a: Type0) (f0: fr r a) (s: nt r a)
  : Lemma (requires distinct (nboxes (fill f0 s)) /\ lends f0.fsib /\ T.Branch? s /\ fred f0)
          (ensures (let p = f0.fbox in
                    let cur = top s in
                    let t0 = fill f0 s in
                    let rot = b2_rot f0.went_right f0.fsib in
                    let u1 = rotn rot t0 in
                    let u2 = recolorn u1 true in
                    let u3 = rcol u2 p false in
                    let u4 = rcol u3 cur true in
                    let (f0', f1') = b2_frames f0 in
                    ST.can_rotate rot (strip t0) /\
                    L.memP p (nboxes u1) /\ sub u1 p == T.Branch (T.left (sub u1 p)) (p, f0.fval) (T.right (sub u1 p)) /\
                    L.memP p (nboxes u2) /\ L.memP cur (nboxes u3) /\
                    top u1 == f1'.fbox /\ ~ (f1'.fbox == p) /\
                    u4 == fill f1' (fill f0' (recolorn s true)) /\
                    (forall (y: B.box r). L.memP y (nboxes u4) <==> L.memP y (nboxes t0))))
  = let p = f0.fbox in
    let T.Branch ql (q, (qk, qc)) qr = f0.fsib in
    let T.Branch sl (cur, sv) sr = s in
    let pv = f0.fval in
    let pv' = (fkey f0, false) in
    let t0 = fill f0 s in
    let rot = b2_rot f0.went_right f0.fsib in
    let u1 = rotn rot t0 in
    let (f0', f1') = b2_frames f0 in
    if f0.went_right then begin
      if nred ql then begin
        let inner = T.Branch qr (p, pv) s in
        let ff = { went_right = true; fbox = q; fval = (qk, true); fsib = recolorn ql false } in
        assert (recolorn u1 true == fill ff inner);
        focus_at [ff] inner;
        let inner' = T.Branch qr (p, pv') s in
        let fp = { went_right = true; fbox = p; fval = pv'; fsib = qr } in
        focus_at [fp; ff] s
      end else begin
        let T.Branch xl (x, (xk, xc)) xr = qr in
        let inner = T.Branch xr (p, pv) s in
        let ff = { went_right = true; fbox = x; fval = (xk, true); fsib = T.Branch ql (q, (qk, qc)) xl } in
        assert (recolorn u1 true == fill ff inner);
        focus_at [ff] inner;
        let fp = { went_right = true; fbox = p; fval = pv'; fsib = xr } in
        focus_at [fp; ff] s
      end
    end else begin
      if nred ql then begin
        let T.Branch xl (x, (xk, xc)) xr = ql in
        let inner = T.Branch s (p, pv) xl in
        let ff = { went_right = false; fbox = x; fval = (xk, true); fsib = T.Branch xr (q, (qk, qc)) qr } in
        assert (recolorn u1 true == fill ff inner);
        focus_at [ff] inner;
        let fp = { went_right = false; fbox = p; fval = pv'; fsib = xl } in
        focus_at [fp; ff] s
      end else begin
        let inner = T.Branch s (p, pv) ql in
        let ff = { went_right = false; fbox = q; fval = (qk, true); fsib = recolorn qr false } in
        assert (recolorn u1 true == fill ff inner);
        focus_at [ff] inner;
        let fp = { went_right = false; fbox = p; fval = pv'; fsib = ql } in
        focus_at [fp; ff] s
      end
    end
#pop-options

#push-options "--fuel 3 --ifuel 2 --z3rlimit 100"
/// The rotated subtree has the same keys, and is red-black of the same black height.
let b2_tree (#r #a: Type0) (f0: fr r a) (s: nt r a)
  : Lemma (requires lends f0.fsib /\ is2 s /\ fred f0 /\ ST.rb (strip (fill f0 s)))
          (ensures (let (f0', f1') = b2_frames f0 in
                    let t = fill f1' (fill f0' (recolorn s true)) in
                    ST.keys (strip t) == ST.keys (strip (fill f0 s)) /\ ST.rb (strip t) /\
                    ST.black_height (strip t) == ST.black_height (strip (fill f0 s)) /\ nred t))
  = let T.Branch ql (q, (qk, qc)) qr = f0.fsib in
    let (f0', f1') = b2_frames f0 in
    let t = fill f1' (fill f0' (recolorn s true)) in
    rb_fill f0 s;
    Seq.lemma_eq_intro (ST.keys (strip t)) (ST.keys (strip (fill f0 s)))
#pop-options

#push-options "--fuel 2 --ifuel 2 --z3rlimit 80"
/// The new frames' keys are on the sides the path takes.
let b2_order (#r #a: Type0) (c: O.comparer a) (k: a) (f0: fr r a) (rest: list (fr r a)) (s: nt r a)
  : Lemma (requires on_rpath c k (f0 :: rest) /\ S.strictly_sorted c (ST.keys (strip (plug (f0 :: rest) s))) /\
                    lends f0.fsib)
          (ensures (let (f0', f1') = b2_frames f0 in
                    f1'.went_right == f0.went_right /\
                    (if f0.went_right then O.compare c k (fkey f1') > 0 else O.compare c k (fkey f1') < 0)))
  = let T.Branch ql (q, (qk, qc)) qr = f0.fsib in
    sib_side c k f0 rest s;
    let kl = ST.keys (strip ql) in
    let kr = ST.keys (strip qr) in
    if f0.went_right then begin
      below_pivot c k kl qk kr;
      if nred ql then () else key_below c k qr
    end else begin
      above_pivot c k kl qk kr;
      if nred ql then key_above c k ql else ()
    end
#pop-options

#push-options "--fuel 2 --ifuel 2 --z3rlimit 80"
let fix_b2 (#r #a: Type0) (c: O.comparer a) (k0: Seq.seq a) (k: a) (f0: fr r a)
    (rest: list (fr r a)) (s: nt r a) (cur par gp mt pom: B.box r) (found: bool)
  : Lemma (requires ok c k0 (plug (f0 :: rest) s) /\ rmid c k (f0 :: rest) s cur par gp mt pom found /\
                    not (is2 f0.fsib))
          (ensures (let p = f0.fbox in
                    let (f0', f1') = b2_frames f0 in
                    let fs' = f0' :: f1' :: rest in
                    let t = fill f1' (fill f0' (recolorn s true)) in
                    lends f0.fsib /\ T.Branch? s /\
                    plug fs' (recolorn s true) == plug rest t /\
                    ok c k0 (plug fs' (recolorn s true)) /\
                    rfx c k fs' (recolorn s true) cur par mt (pom_a p mt f1'.fbox pom) found))
  = let p = f0.fbox in
    let t0 = fill f0 s in
    let (f0', f1') = b2_frames f0 in
    let t = fill f1' (fill f0' (recolorn s true)) in
    rb_plug_sub rest t0;
    rb_fill f0 s;
    distinct_plug rest t0;
    b2_shape f0 s;
    b2_tree f0 s;
    swap_boxes rest t0 t;
    keys_plug rest t0 t;
    rb_replace rest t0 t;
    sorted_plug_sub c rest t0;
    b2_order c k f0 rest s;
    mfind_mem c k rest;
    mstate_head c k f0 rest s mt pom found;
    assert (~ (L.memP f1'.fbox (fboxes rest)))
#pop-options

(* ------------------------------------------------------------------------------------ *)
(* One step down, and the end of the search                                              *)

/// `order`: `-1` once the match is found, and otherwise the comparison with `current`.
let rord (#r #a: Type0) (c: O.comparer a) (k: a) (s: nt r a) (found: bool) : int =
  if found then -1 else cmp c k (nkey s k)

/// The child the search goes on to, and the frame it leaves.
let rchild (#r #a: Type0) (s: nt r a) (o: int) : nt r a =
  match s with T.Leaf -> T.Leaf | T.Branch l _ rr -> if o < 0 then l else rr

let rframe (#r #a: Type0) (s: nt r a{T.Branch? s}) (o: int) : fr r a =
  let T.Branch l (b, v) rr = s in
  { went_right = o >= 0; fbox = b; fval = v; fsib = (if o < 0 then rr else l) }

let rframe_fill (#r #a: Type0) (s: nt r a{T.Branch? s}) (o: int)
  : Lemma (ensures fill (rframe s o) (rchild s o) == s)
  = ()

#push-options "--fuel 2 --ifuel 2 --z3rlimit 60"
/// After the fix-up, `current` moves down: the invariant holds one level lower, at a
/// smaller subtree.
let step (#r #a: Type0) (c: O.comparer a) (k0: Seq.seq a) (k: a) (fs: list (fr r a)) (s: nt r a)
    (cur par mt pom: B.box r) (found: bool)
  : Lemma (requires ok c k0 (plug fs s) /\ rfx c k fs s cur par mt pom found)
          (ensures (let o = rord c k s found in
                    let fs' = rframe s o :: fs in
                    let found' = found || o = 0 in
                    let mt' = if o = 0 then cur else mt in
                    let pom' = if o = 0 then par else pom in
                    plug fs' (rchild s o) == plug fs s /\
                    T.size (rchild s o) < T.size s /\
                    (found ==> o == -1) /\ (o = 0 ==> found == false) /\
                    rinv c k fs' (rchild s o) (top (rchild s o)) cur par mt' pom' found'))
  = let T.Branch l (b, (sk, sc)) rr = s in
    let o = rord c k s found in
    sorted_plug_sub c fs s;
    if found then begin
      found_above c k fs s;
      key_above c k s
    end else on_path_of c k fs
#pop-options

/// The search ended without a match: the key is not there.
let end_none (#r #a: Type0) (c: O.comparer a) (k0: Seq.seq a) (k: a) (fs: list (fr r a))
    (s: nt r a) (cur par gp mt pom: B.box r) (found: bool)
  : Lemma (requires ok c k0 (plug fs s) /\ rinv c k fs s cur par gp mt pom found /\ s == T.Leaf /\
                    B.is_null mt)
          (ensures found == false /\ S.key_index c k0 k < 0)
  = mfind_mem c k fs;
    (match mfind c k fs with
     | Some (m, _) -> mem_plug m fs s
     | None -> ());
    on_path_of c k fs;
    contains_plug c k fs s
