module SortedSetInductive.Item.Spec

module O = SortedSetInductive.Ownership
module N = Class_Node
module T = Pulse.Lib.CSharp.Tree
module ST = Pulse.Lib.CSharp.SearchTree
module P = Pulse.Lib.CSharp.RegionPath
module E = Pulse.Lib.CSharp.RefEq
module RR = Pulse.Lib.CSharp.RegionReplace
module D = Pulse.Lib.CSharp.TopDown
module Seq = FStar.Seq

#set-options "--z3rlimit 10"

// Change one payload, never a pointer or a colour. These are operations on
// inductive labelled trees; no heap map or region resource is introduced.
let updated (#a: Type0) (t: O.tree a) (x: N.class_Node__opt a) (item: a) : Tot (O.tree a) =
  P.bmap (fun n e -> if E.ref_eq n x then (item, snd e) else e) t

let updated_labels (#a: Type0) (t: O.tree a) (x: N.class_Node__opt a) (item: a)
  : Lemma (
      P.nboxes (updated t x item) == P.nboxes t /\
      O.top (updated t x item) == O.top t /\
      (O.good t ==> O.good (updated t x item))) =
  let f = fun n e -> if E.ref_eq n x then (item, snd e) else e in
  P.nboxes_bmap f t;
  P.top_bmap f t

let rec updated_shape (#a: Type0) (t: O.tree a) (x: N.class_Node__opt a) (item: a)
  : Lemma (RR.same_shape (O.values (updated t x item)) (O.values t))
      (decreases t) =
  match t with
  | T.Leaf -> ()
  | T.Branch l _ r ->
    updated_shape l x item;
    updated_shape r x item

let updated_balanced (#a: Type0) (t: O.tree a) (x: N.class_Node__opt a) (item: a)
  : Lemma (
      ST.red_black (O.values (updated t x item)) == ST.red_black (O.values t) /\
      T.size (O.values (updated t x item)) == T.size (O.values t)) =
  updated_shape t x item;
  RR.same_shape_rb (O.values (updated t x item)) (O.values t)

let rec updated_outside (#a: Type0) (t: O.tree a) (x: N.class_Node__opt a) (item: a)
  : Lemma (requires (~ (O.member t x))) (ensures updated t x item == t) (decreases t) =
  match t with
  | T.Leaf -> ()
  | T.Branch l _ r ->
    updated_outside l x item;
    updated_outside r x item

let rec position (#a: Type0) (t: O.tree a) (x: N.class_Node__opt a)
  : Tot nat (decreases t) =
  match t with
  | T.Leaf -> 0
  | T.Branch l (b, _) r ->
    if E.ref_eq b x then T.size l
    else if P.mem_box x l then position l x
    else T.size l + 1 + position r x

let sub_step (#a: Type0) (l r: O.tree a) (b x: N.class_Node__opt a) (entry: a & bool)
  : Lemma (
      P.sub (T.Branch l (b, entry) r) x ==
        (if E.ref_eq b x then T.Branch l (b, entry) r
         else if P.mem_box x l then P.sub l x else P.sub r x)) =
  P.focus_acc_app l x [{ P.went_right=false; P.fbox=b; P.fval=entry; P.fsib=r }];
  P.focus_acc_app r x [{ P.went_right=true; P.fbox=b; P.fval=entry; P.fsib=l }]

let rec updated_keys (#a: Type0) (t: O.tree a) (x: N.class_Node__opt a) (item: a)
  : Lemma (requires O.good t /\ O.member t x)
      (ensures (
        let i = position t x in
        let s = ST.keys (O.values t) in
        i < Seq.length s /\
        Seq.index s i == ST.root_key (O.lookup t x) item /\
        Seq.equal (ST.keys (O.values (updated t x item))) (Seq.upd s i item)))
      (decreases t) =
  match t with
  | T.Branch l (b, entry) r ->
    D.distinct_nbranch l b entry r;
    D.size_strip l;
    sub_step l r b x entry;
    P.mem_box_nboxes x l;
    let sl = ST.keys (O.values l) in
    let sr = ST.keys (O.values r) in
    if E.ref_eq b x then begin
      updated_outside l x item;
      updated_outside r x item;
      Seq.lemma_eq_intro (Seq.append sl (Seq.cons item sr))
        (Seq.upd (Seq.append sl (Seq.cons (fst entry) sr)) (Seq.length sl) item)
    end else if P.mem_box x l then begin
      updated_keys l x item;
      updated_outside r x item;
      RR.append_upd_left sl (Seq.cons (fst entry) sr) (position l x) item
    end else begin
      updated_keys r x item;
      updated_outside l x item;
      RR.cons_upd (fst entry) sr (position r x) item;
      RR.append_upd_right sl (Seq.cons (fst entry) sr) (position r x + 1) item
    end

let equivalent (#a: Type0) (c: Pulse.Lib.CSharp.Order.comparer a) (before after: a) =
  forall (z: a). Pulse.Lib.CSharp.Order.compare c after z ==
    Pulse.Lib.CSharp.Order.compare c before z

let updated_sorted (#a: Type0) (t: O.tree a) (x: N.class_Node__opt a)
    (c: Pulse.Lib.CSharp.Order.comparer a) (before item: a)
  : Lemma (requires O.good t /\ O.member t x /\
      Pulse.Lib.CSharp.Sorted.strictly_sorted c (ST.keys (O.values t)) /\
      before == ST.root_key (O.lookup t x) before /\ equivalent c before item)
    (ensures Pulse.Lib.CSharp.Sorted.strictly_sorted c (ST.keys (O.values (updated t x item)))) =
  updated_keys t x before;
  updated_keys t x item;
  RR.upd_equiv c (ST.keys (O.values t)) (position t x) item
