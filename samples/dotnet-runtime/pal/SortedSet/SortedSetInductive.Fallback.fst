module SortedSetInductive.Fallback

module O = Pulse.Lib.CSharp.Order
module T = Pulse.Lib.CSharp.Tree
module ST = Pulse.Lib.CSharp.SearchTree
module D = Pulse.Lib.CSharp.TopDown
module P = Pulse.Lib.CSharp.RegionPath
module R = Pulse.Lib.CSharp.Region
module B = Pulse.Lib.Box
module L = FStar.List.Tot
module Seq = FStar.Seq
module S = Pulse.Lib.CSharp.Sorted
module Count = SortedSetCount

let rec find_equivalent (#a #b: Type0) (c: O.comparer a) (t: T.tree (a & b)) (x: a)
  : Lemma (ensures O.compare c (ST.find c t x x) x == 0)
          (decreases t)
  = match t with
    | T.Leaf -> O.compare_refl c x
    | T.Branch l (v, _) r ->
      let order = O.compare c x v in
      if order = 0 then O.compare_antisym c x v
      else if order < 0 then find_equivalent c l x
      else find_equivalent c r x

let rec node_index (#r #a: Type0) (t: D.nt r a) (x: B.box r)
  : Tot int (decreases t) =
  match t with
  | T.Leaf -> -1
  | T.Branch l (b, _) rr ->
    if R.eq_box b x then Seq.length (ST.keys (D.strip l))
    else if P.mem_box x l then node_index l x
    else Seq.length (ST.keys (D.strip l)) + 1 + node_index rr x

let rec node_index_key (#r #a: Type0) (t: D.nt r a) (x: B.box r) (d: a)
  : Lemma (requires L.memP x (P.nboxes t))
          (ensures (let i = node_index t x in
                    0 <= i /\ i < Seq.length (ST.keys (D.strip t)) /\
                    T.Branch? (P.sub t x) /\
                    ST.root_key (D.strip (P.sub t x)) d == Seq.index (ST.keys (D.strip t)) i))
          (decreases t)
  = match t with
    | T.Branch l (b, v) rr ->
      if R.eq_box b x then ()
      else if P.mem_box x l then begin
        node_index_key l x d;
        P.focus_acc_app l x [{ P.went_right = false; P.fbox = b; P.fval = v; P.fsib = rr }]
      end else begin
        node_index_key rr x d;
        P.focus_acc_app rr x [{ P.went_right = true; P.fbox = b; P.fval = v; P.fsib = l }]
      end

let rec node_index_injective (#r #a: Type0) (t: D.nt r a) (x y: B.box r) (d: a)
  : Lemma (requires L.memP x (P.nboxes t) /\ L.memP y (P.nboxes t) /\
                    node_index t x == node_index t y)
          (ensures x == y)
          (decreases t)
  = match t with
    | T.Branch l (b, _) rr ->
      if R.eq_box b x then begin
        if R.eq_box b y then ()
        else if P.mem_box y l then node_index_key l y d
        else node_index_key rr y d
      end else if P.mem_box x l then begin
        node_index_key l x d;
        if R.eq_box b y then ()
        else if P.mem_box y l then node_index_injective l x y d
        else node_index_key rr y d
      end else begin
        node_index_key rr x d;
        if R.eq_box b y then ()
        else if P.mem_box y l then node_index_key l y d
        else node_index_injective rr x y d
      end

let node_key_injective (#r #a: Type0) (c: O.comparer a) (t: D.nt r a)
    (x y: B.box r) (d: a)
  : Lemma (requires S.strictly_sorted c (ST.keys (D.strip t)) /\
                    L.memP x (P.nboxes t) /\ L.memP y (P.nboxes t) /\
                    O.compare c (ST.root_key (D.strip (P.sub t x)) d)
                                (ST.root_key (D.strip (P.sub t y)) d) == 0)
          (ensures x == y)
  = node_index_key t x d;
    node_index_key t y d;
    Count.key_index_index c (ST.keys (D.strip t)) (node_index t x);
    Count.key_index_unique c (ST.keys (D.strip t))
      (ST.root_key (D.strip (P.sub t x)) d) (node_index t y);
    node_index_injective t x y d

let rec hit_equivalent (#a: Type0) (c: O.comparer a) (s: Seq.seq a) (x y: a)
  : Lemma (requires O.compare c x y == 0)
          (ensures Count.hit c s x == Count.hit c s y)
          (decreases Seq.length s)
  = if Seq.length s > 0 then begin
      Count.equiv_sign c x y (Seq.last s);
      hit_equivalent c (Count.init s) x y
    end

let lookup_equivalent (#r #a: Type0) (c: O.comparer a) (t: D.nt r a)
    (node p: B.box r) (item d: a)
  : Lemma (requires S.strictly_sorted c (ST.keys (D.strip t)) /\
                    L.memP node (P.nboxes t) /\ L.memP p (P.nboxes t) /\
                    O.compare c (ST.root_key (D.strip (P.sub t node)) item) item == 0)
          (ensures (O.compare c item (ST.root_key (D.strip (P.sub t p)) d) == 0)
                   <==> node == p)
  = node_index_key t node item;
    node_index_key t p d;
    let key = ST.root_key (D.strip (P.sub t p)) d in
    if R.eq_box node p then Count.equiv_sym c key item
    else if O.compare c item key = 0 then begin
      Count.equiv_trans c (ST.root_key (D.strip (P.sub t node)) item) item key;
      node_key_injective c t node p item
    end

let rec node_mem (#r: Type0) (nodes: Seq.seq (B.box r)) (node: B.box r)
  : Tot bool (decreases Seq.length nodes) =
  Seq.length nodes > 0 &&
    (R.eq_box (Seq.last nodes) node || node_mem (Count.init nodes) node)

let seen_matches (#r #a: Type0) (c: O.comparer a) (ok: a -> bool) (t: D.nt r a)
    (items: Seq.seq a) (nodes: Seq.seq (B.box r)) : prop =
  forall (p: B.box r) (d: a). L.memP p (P.nboxes t) /\ ok (ST.root_key (D.strip (P.sub t p)) d) ==>
    node_mem nodes p == Count.hit c items (ST.root_key (D.strip (P.sub t p)) d)

let seen_empty (#r #a: Type0) (c: O.comparer a) (ok: a -> bool) (t: D.nt r a)
    (items: Seq.seq a) (nodes: Seq.seq (B.box r))
  : Lemma (requires Seq.length items == 0 /\ Seq.length nodes == 0)
          (ensures seen_matches c ok t items nodes)
  = ()

let seen_lookup (#r #a: Type0) (c: O.comparer a) (ok: a -> bool) (t: D.nt r a)
    (items: Seq.seq a) (nodes: Seq.seq (B.box r)) (node: B.box r) (item: a)
  : Lemma (requires seen_matches c ok t items nodes /\ L.memP node (P.nboxes t) /\
                    ok (ST.root_key (D.strip (P.sub t node)) item) /\
                    O.compare c (ST.root_key (D.strip (P.sub t node)) item) item == 0)
          (ensures node_mem nodes node == Count.hit c items item)
  = hit_equivalent c items (ST.root_key (D.strip (P.sub t node)) item) item

let seen_step (#r #a: Type0) (c: O.comparer a) (ok: a -> bool) (t: D.nt r a)
    (items: Seq.seq a) (before after: Seq.seq (B.box r)) (node: B.box r) (item: a)
  : Lemma (requires S.strictly_sorted c (ST.keys (D.strip t)) /\
                    seen_matches c ok t items before /\ L.memP node (P.nboxes t) /\
                    O.compare c (ST.root_key (D.strip (P.sub t node)) item) item == 0 /\
                    (forall (p: B.box r). node_mem after p == (R.eq_box p node || node_mem before p)))
          (ensures seen_matches c ok t (Seq.snoc items item) after)
  = let aux (p: B.box r) (d: a)
      : Lemma (L.memP p (P.nboxes t) /\ ok (ST.root_key (D.strip (P.sub t p)) d) ==>
          node_mem after p == Count.hit c (Seq.snoc items item) (ST.root_key (D.strip (P.sub t p)) d))
      = if P.mem_box p t then begin
          lookup_equivalent c t node p item d;
          Count.hit_snoc c items item (ST.root_key (D.strip (P.sub t p)) d)
        end in
    FStar.Classical.forall_intro_2 aux

let seen_miss (#r #a: Type0) (c: O.comparer a) (ok: a -> bool) (t: D.nt r a)
    (items: Seq.seq a) (nodes: Seq.seq (B.box r)) (item: a)
  : Lemma (requires S.strictly_sorted c (ST.keys (D.strip t)) /\
                    (forall (x y: a). O.compare c x y == 0 ==> ok x == ok y) /\
                    seen_matches c ok t items nodes /\
                    not (ok item && S.key_index c (ST.keys (D.strip t)) item >= 0))
          (ensures seen_matches c ok t (Seq.snoc items item) nodes)
  = let aux (p: B.box r) (d: a)
      : Lemma (L.memP p (P.nboxes t) /\ ok (ST.root_key (D.strip (P.sub t p)) d) ==>
          node_mem nodes p == Count.hit c (Seq.snoc items item) (ST.root_key (D.strip (P.sub t p)) d))
      = if P.mem_box p t then begin
          let key = ST.root_key (D.strip (P.sub t p)) d in
          node_index_key t p d;
          Count.hit_snoc c items item key;
          if O.compare c item key = 0 then begin
            Count.ok_equiv c ok item key;
            Count.key_index_unique c (ST.keys (D.strip t)) item (node_index t p)
          end
        end in
    FStar.Classical.forall_intro_2 aux

let count_step (#a: Type0) (c: O.comparer a) (ok: a -> bool)
    (keys items: Seq.seq a) (item: a)
  : Lemma (requires S.strictly_sorted c keys /\
                    (forall (x y: a). O.compare c x y == 0 ==> ok x == ok y))
          (ensures (let present = ok item && S.key_index c keys item >= 0 in
                    Count.found c ok keys (Seq.snoc items item) ==
                      Count.found c ok keys items + (if present && not (Count.hit c items item) then 1 else 0) /\
                    Count.unfound c ok keys (Seq.snoc items item) ==
                      Count.unfound c ok keys items + (if present then 0 else 1)))
  = Count.init_snoc items item;
    Count.found_upto_snoc c ok keys items item (Seq.length keys);
    let i = S.key_index c keys item in
    if i >= 0 then hit_equivalent c items (Seq.index keys i) item

let count_inv (#a: Type0) (c: O.comparer a) (ok: a -> bool)
    (keys all: Seq.seq a) (i unique unfound: int) : prop =
  0 <= i /\ i <= Seq.length all /\ 0 <= unique /\ 0 <= unfound /\
  unique + unfound <= i /\
  unique == Count.found c ok keys (Seq.slice all 0 i) /\
  unfound == Count.unfound c ok keys (Seq.slice all 0 i)

let count_start (#a: Type0) (c: O.comparer a) (ok: a -> bool) (keys all: Seq.seq a)
  : Lemma (count_inv c ok keys all 0 0 0)
  = Count.found_empty c ok keys (Seq.slice all 0 0)

let count_loop_step (#a: Type0) (c: O.comparer a) (ok: a -> bool)
    (keys all: Seq.seq a) (i unique unfound: int)
  : Lemma (requires S.strictly_sorted c keys /\
                    (forall (x y: a). O.compare c x y == 0 ==> ok x == ok y) /\
                    count_inv c ok keys all i unique unfound /\ i < Seq.length all)
          (ensures (let item = Seq.index all i in
                    let present = ok item && S.key_index c keys item >= 0 in
                    let seen = Count.hit c (Seq.slice all 0 i) item in
                    count_inv c ok keys all (i + 1)
                      (unique + (if present && not seen then 1 else 0))
                      (unfound + (if present then 0 else 1))))
  = Count.slice_snoc all i;
    count_step c ok keys (Seq.slice all 0 i) (Seq.index all i)

let count_done (#a: Type0) (c: O.comparer a) (ok: a -> bool)
    (keys all: Seq.seq a) (i unique unfound: int) (return_if_unfound: bool)
  : Lemma (requires count_inv c ok keys all i unique unfound /\
                    (i == Seq.length all \/ (return_if_unfound /\ unfound > 0)))
          (ensures unfound >= 0 /\
                   (unfound > 0 <==> Count.unfound c ok keys all > 0) /\
                   (not return_if_unfound \/ unfound == 0 ==> unique == Count.found c ok keys all))
  = Count.unfound_mono c ok keys all i;
    if i = Seq.length all then Seq.lemma_eq_intro (Seq.slice all 0 i) all
