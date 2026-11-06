module Pulse.Lib.CSharp.TopDownSucc

/// R27.30. The end of `SortedSet<T>.DoRemove`: the matching node replaced by its in-order
/// successor (`ReplaceNode`), over the boxed trees of `TopDown`. The descent of
/// `TopDownRemove` ends at a leaf; if it met the key, the last node it passed is the match's
/// successor (the leftmost node of the match's right subtree, or the match itself when that
/// subtree is empty), and the descent made it not a 2-node. `rdel` is the replacement;
/// `end_found` proves it removes exactly the key and keeps the tree red-black. Everything is
/// proved here without admits.

open Pulse.Lib.CSharp.Region
open Pulse.Lib.CSharp.RegionTree
open Pulse.Lib.CSharp.RegionPath
open Pulse.Lib.CSharp.TopDown
open Pulse.Lib.CSharp.TopDownRemove
module B = Pulse.Lib.Box
module L = FStar.List.Tot
module T = Pulse.Lib.CSharp.Tree
module O = Pulse.Lib.CSharp.Order
module S = Pulse.Lib.CSharp.Sorted
module ST = Pulse.Lib.CSharp.SearchTree
module Seq = FStar.Seq

(* ------------------------------------------------------------------------------------ *)
(* The leftmost node                                                                     *)

/// The path from a tree's root down to its leftmost node, innermost first.
let rec lspine (#r #a: Type0) (t: nt r a) : Tot (list (fr r a)) (decreases t) =
  match t with
  | T.Leaf -> []
  | T.Branch l (b, v) rr ->
    if T.Branch? l then L.append (lspine l) [{ went_right = false; fbox = b; fval = v; fsib = rr }]
    else []

/// The subtree at the leftmost node.
let rec lmin (#r #a: Type0) (t: nt r a) : Tot (nt r a) (decreases t) =
  match t with
  | T.Leaf -> T.Leaf
  | T.Branch l _ _ -> if T.Branch? l then lmin l else t

let rec lspine_plug (#r #a: Type0) (fs: list (fr r a)) (t: nt r a)
  : Lemma (requires all_left fs /\ T.Branch? t)
          (ensures lspine (plug fs t) == L.append (lspine t) fs /\ lmin (plug fs t) == lmin t)
          (decreases fs)
  = match fs with
    | [] -> L.append_l_nil (lspine t)
    | f :: rest ->
      frame_eta f;
      lspine_plug rest (fill f t);
      L.append_assoc (lspine t) [f] rest

(* ------------------------------------------------------------------------------------ *)
(* The replacement                                                                       *)

/// `ReplaceNode` before the match's colour is copied: the match's left subtree if its
/// right one is empty, and otherwise the successor over the match's left subtree and the
/// right one without the successor (its right child blackened in its place).
let pre_col (#r #a: Type0) (m: nt r a) : nt r a =
  match m with
  | T.Leaf -> T.Leaf
  | T.Branch ml _ mr ->
    match lmin mr with
    | T.Leaf -> ml
    | T.Branch _ (sb, sv) sr -> T.Branch ml (sb, sv) (plug (lspine mr) (recolorn sr false))

/// The tree after `ReplaceNode(match, ...)`.
let rdel (#r #a: Type0) (n: nt r a) (mt: B.box r) : nt r a =
  let m = sub n mt in
  replace n mt (recolorn (pre_col m) (nred m))

/// `ReplaceNode`'s `successor` argument: the match's successor, or the match itself.
let succ_of (#r #a: Type0) (m: nt r a) : B.box r =
  match m with
  | T.Leaf -> B.null
  | T.Branch _ (b, _) mr -> if T.Branch? mr then top (lmin mr) else b

/// `parentOfSuccessor`, when the match has a right subtree.
let pos_of (#r #a: Type0) (m: nt r a) : B.box r =
  match m with
  | T.Leaf -> B.null
  | T.Branch _ (b, _) mr -> (match lspine mr with [] -> b | g :: _ -> g.fbox)

/// What `ReplaceNode` is called with: the tree is `ok`; `mt` is a node of it, `pom` its
/// parent, `succ` and `pos` as above; the successor is not a 2-node (`ReplaceNode`'s
/// `Debug.Assert`s); and the replacement removes `k`.
let rpre (#r #a: Type0) (c: O.comparer a) (k0: Seq.seq a) (k: a) (n: nt r a)
    (mt pom succ pos: B.box r) : prop =
  ok c k0 n /\ L.memP mt (nboxes n) /\ S.key_index c k0 k >= 0 /\
  (let m = sub n mt in
   T.Branch? m /\ top m == mt /\ pom == fb (fst (focus n mt)) 0 /\ succ == succ_of m /\
   (T.Leaf? (T.right m) ==> T.Leaf? (pre_col m) \/ nred (pre_col m)) /\
   (T.Branch? (T.right m) ==>
      pos == pos_of m /\ B.is_null pos == false /\
      (let s = lmin (T.right m) in
       T.Leaf? (T.left s) /\
       ((T.Leaf? (T.right s) /\ nred s) \/ (nred (T.right s) /\ not (nred s))))) /\
   ok c (removed c k0 k) (rdel n mt))

(* ------------------------------------------------------------------------------------ *)
(* The match on the path                                                                 *)

/// The path split at its innermost frame equivalent to `k`.
let rec msplit (#r #a: Type0) (c: O.comparer a) (k: a) (fs: list (fr r a))
  : Tot (option (list (fr r a) & fr r a & list (fr r a))) (decreases fs)
  = match fs with
    | [] -> None
    | f :: rest ->
      if O.compare c k (fkey f) = 0 then Some ([], f, rest)
      else match msplit c k rest with
           | Some (i, m, o) -> Some (f :: i, m, o)
           | None -> None

let rec msplit_props (#r #a: Type0) (c: O.comparer a) (k: a) (fs: list (fr r a))
  : Lemma (requires on_rpath c k fs)
          (ensures (match msplit c k fs, mfind c k fs with
                    | Some (i, m, o), Some (b, pb) ->
                      fs == L.append i (m :: o) /\ m.fbox == b /\ fb o 0 == pb /\
                      O.compare c k (fkey m) == 0 /\ on_rpath c k i /\ on_rpath c k (m :: o)
                    | None, None -> True
                    | _ -> False))
          (decreases fs)
  = match fs with
    | [] -> ()
    | f :: rest -> if O.compare c k (fkey f) = 0 then () else msplit_props c k rest

let rec fb_append (#r #a: Type0) (i: list (fr r a)) (m: fr r a) (o: list (fr r a))
  : Lemma (ensures fb (L.append i (m :: o)) (L.length i) == m.fbox) (decreases i)
  = match i with [] -> () | _ :: t -> fb_append t m o

(* ------------------------------------------------------------------------------------ *)
(* Red-black facts                                                                       *)

let bh0_leaf (#r #a: Type0) (t: nt r a)
  : Lemma (requires ST.rb (strip t) /\ ST.black_height (strip t) == 0 /\ not (nred t))
          (ensures T.Leaf? t)
  = ()

/// Below a frame, the top colour does not depend on the subtree.
let rec nred_plug (#r #a: Type0) (fs: list (fr r a)) (s s': nt r a)
  : Lemma (requires Cons? fs) (ensures nred (plug fs s) == nred (plug fs s')) (decreases fs)
  = match fs with
    | [_] -> ()
    | f :: rest -> nred_plug rest (fill f s) (fill f s')

/// A leaf-children-free node of black height 0 swapped for its blackened right child.
let succ_rb (#r #a: Type0) (s: nt r a)
  : Lemma (requires ST.rb (strip s) /\ T.Branch? s /\ T.Leaf? (T.left s) /\
                    (nred s || nred (T.right s)))
          (ensures (let sr' = recolorn (T.right s) false in
                    ST.rb (strip sr') /\ not (nred sr') /\
                    ST.black_height (strip sr') == ST.black_height (strip s) /\
                    ((T.Leaf? (T.right s) /\ nred s) \/ (nred (T.right s) /\ not (nred s)))))
  = let T.Branch _ _ sr = s in
    if nred s then bh0_leaf sr

(* ------------------------------------------------------------------------------------ *)
(* The end of the search                                                                 *)

let keys_cons (#a: Type0) (v: a) (ks: Seq.seq a)
  : Lemma (ensures Seq.append Seq.empty (Seq.cons v ks) == Seq.cons v ks)
  = Seq.append_empty_l (Seq.cons v ks)

#push-options "--fuel 2 --ifuel 2 --z3rlimit 120"
/// The replacement at a match whose right subtree is empty.
let end_r0 (#r #a: Type0) (c: O.comparer a) (k0: Seq.seq a) (k: a) (fm: fr r a)
    (outer: list (fr r a))
  : Lemma (requires ok c k0 (plug outer (fill fm T.Leaf)) /\ fm.went_right /\
                    O.compare c k (fkey fm) == 0 /\ (fred fm || nred fm.fsib))
          (ensures (let m = fill fm T.Leaf in
                    let m' = recolorn (pre_col m) (nred m) in
                    S.key_index c k0 k >= 0 /\
                    (T.Leaf? (pre_col m) \/ nred (pre_col m)) /\
                    ok c (removed c k0 k) (plug outer m')))
  = let m = fill fm T.Leaf in
    let ml = fm.fsib in
    let m' = recolorn (pre_col m) (nred m) in
    assert (pre_col m == ml);
    rb_plug_sub outer m;
    if fred fm then bh0_leaf ml;
    rb_replace outer m m';
    Seq.append_empty_r (ST.keys (strip ml));
    let sa = ST.keys (strip ml) in
    assert (ST.keys (strip m) == Seq.append sa (Seq.cons (fkey fm) Seq.empty));
    assert (ST.keys (strip m') == Seq.append sa Seq.empty);
    let (pa, pb) = keys_del_plug outer m m' sa (fkey fm) Seq.empty in
    key_index_pivot c pa (fkey fm) pb k;
    distinct_plug outer m; distinct_plug outer m'
#pop-options

#push-options "--fuel 2 --ifuel 2 --z3rlimit 200"
/// The replacement at a match with a right subtree `plug gs s`, `s` the successor.
let end_r1 (#r #a: Type0) (c: O.comparer a) (k0: Seq.seq a) (k: a) (fm: fr r a)
    (outer: list (fr r a)) (gs: list (fr r a)) (s: nt r a)
  : Lemma (requires ok c k0 (plug outer (fill fm (plug gs s))) /\ fm.went_right /\ all_left gs /\
                    O.compare c k (fkey fm) == 0 /\ T.Branch? s /\ T.Leaf? (T.left s) /\
                    (nred s || nred (T.right s)))
          (ensures (let mr = plug gs s in
                    let m = fill fm mr in
                    let m' = recolorn (pre_col m) (nred m) in
                    lspine mr == gs /\ lmin mr == s /\
                    S.key_index c k0 k >= 0 /\
                    ((T.Leaf? (T.right s) /\ nred s) \/ (nred (T.right s) /\ not (nred s))) /\
                    ok c (removed c k0 k) (plug outer m')))
  = let mr = plug gs s in
    let m = fill fm mr in
    let ml = fm.fsib in
    let T.Branch _ (sb, (sk, sc)) sr = s in
    let sr' = recolorn sr false in
    lspine_plug gs s;
    let mr' = plug gs sr' in
    let m' = recolorn (pre_col m) (nred m) in
    assert (m' == T.Branch ml (sb, (sk, fred fm)) mr');
    rb_plug_sub outer m;
    rb_plug_sub gs s;
    succ_rb s;
    rb_replace gs s sr';
    bh_plug gs s sr';
    (match gs with [] -> () | _ -> nred_plug gs s sr');
    rb_replace outer m m';
    keys_cons sk (ST.keys (strip sr));
    keys_left_plug gs s sr' sk;
    let sa = ST.keys (strip ml) in
    let sb = Seq.cons sk (ST.keys (strip mr')) in
    let (pa, pb) = keys_del_plug outer m m' sa (fkey fm) sb in
    key_index_pivot c pa (fkey fm) pb k;
    distinct_plug outer m; distinct_plug gs s; distinct_plug gs sr';
    assert (distinct (nboxes m'));
    assert (forall (y: B.box r). L.memP y (nboxes m') ==> L.memP y (nboxes m));
    distinct_plug outer m'
#pop-options

#push-options "--fuel 2 --ifuel 2 --z3rlimit 120"
/// The search met `k` and ended at a leaf: `ReplaceNode`'s precondition holds.
let end_found (#r #a: Type0) (c: O.comparer a) (k0: Seq.seq a) (k: a) (fs: list (fr r a))
    (s: nt r a) (cur par gp mt pom: B.box r) (found: bool)
  : Lemma (requires ok c k0 (plug fs s) /\ rinv c k fs s cur par gp mt pom found /\ s == T.Leaf /\
                    B.is_null mt == false)
          (ensures found == true /\ rpre c k0 k (plug fs s) mt pom par gp)
  = msplit_props c k fs;
    let Some (inner, fm, outer) = msplit c k fs in
    let n = plug fs s in
    let mr = plug inner s in
    let m = fill fm mr in
    plug_append inner (fm :: outer) s;
    assert (n == plug outer m);
    focus_at outer m;
    found_above c k (fm :: outer) mr;
    left_past c k inner s;
    match inner with
    | [] -> end_r0 c k0 k fm outer
    | f0 :: gs ->
      let sx = fill f0 T.Leaf in
      plug_append [f0] gs T.Leaf;
      assert (mr == plug gs sx);
      end_r1 c k0 k fm outer gs sx;
      (match gs with
       | [] -> ()
       | g :: _ -> assert (L.memP g.fbox (nboxes n)))
#pop-options
