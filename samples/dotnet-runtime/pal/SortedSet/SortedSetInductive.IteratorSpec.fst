module SortedSetInductive.IteratorSpec

module Seq = FStar.Seq
module CS = Pulse.Lib.CSharp.Seq
module O = Pulse.Lib.CSharp.Order
module RW = Pulse.Lib.CSharp.RangeWalk
module Q = SortedSetInductive.State
module Own = SortedSetInductive.Ownership
module W = SortedSetInductive.StateWalk
module F = SortedSetInductive.StateFacts
module B = Pulse.Lib.Box
module N = Class_Node
module Walk = Pulse.Lib.CSharp.RegionWalk
module ST = Pulse.Lib.CSharp.SearchTree
module T = Pulse.Lib.CSharp.Tree
module S = Pulse.Lib.CSharp.Sorted
module C = SortedSetCount

#set-options "--z3rlimit 10"

let current_items (#a: Type0) (t: T.tree (a & bool)) : Seq.seq a =
  match t with
  | T.Leaf -> Seq.empty
  | T.Branch _ (x, _) _ -> Seq.create 1 x

// Optional bounds avoid manufacturing an inhabitant of the element type
// for an ordinary (unbounded) set. Empty or disabled bounds need no key.
let filter (#a: Type0) (c: O.comparer a) (lo hi: Seq.seq a)
    (la ua: bool) (s: Seq.seq a) : Tot (Seq.seq a) =
  if not la && not ua then s
  else if Seq.length s = 0 then s
  else
    let l = if Seq.length lo > 0 then Seq.index lo 0 else Seq.index s 0 in
    let h = if Seq.length hi > 0 then Seq.index hi 0 else Seq.index s 0 in
    RW.filter c l h la ua s

let inside (#a: Type0) (c: O.comparer a) (lo hi: Seq.seq a)
    (la ua: bool) (x: a) : prop =
  (if la then Seq.length lo > 0 /\ O.compare c (Seq.index lo 0) x <= 0 else True) /\
  (if ua then Seq.length hi > 0 /\ O.compare c x (Seq.index hi 0) <= 0 else True)

// Only in-range roots are pushed. Consequently a nonempty stack yields a
// logical element even when the unfiltered far subtrees contain excluded keys.
let walkable (#a: Type0) (c: O.comparer a) (lo hi: Seq.seq a)
    (la ua: bool) (h: Q.observation a) (stack: Seq.seq (Class_Node.class_Node__opt a)) : prop =
  Q.walkable h stack /\
  (if not la && not ua then True
   else (forall (i: nat). i < Seq.length stack ==>
     (match Q.find h (Seq.index stack i) with
     | None -> False
     | Some r -> inside c lo hi la ua (fst (Own.entry r)) /\
         S.strictly_sorted c (ST.keys (Q.tree_at h (Seq.index stack i))))))

let bounds = C.bounded

let rec range_filter_bounds (#a: Type0) (c: O.comparer a)
    (l h l' h': a) (la ua: bool) (s: Seq.seq a)
  : Lemma (requires (la ==> l == l') /\ (ua ==> h == h'))
      (ensures RW.filter c l h la ua s == RW.filter c l' h' la ua s)
      (decreases Seq.length s) =
  if Seq.length s = 0 then ()
  else range_filter_bounds c l h l' h' la ua (Seq.tail s)

let rec range_filter_unbounded (#a: Type0) (c: O.comparer a) (l h: a) (s: Seq.seq a)
  : Lemma (ensures RW.filter c l h false false s == s)
      (decreases Seq.length s) =
  if Seq.length s = 0 then Seq.lemma_eq_intro s Seq.empty
  else (
    range_filter_unbounded c l h (Seq.tail s);
    Seq.lemma_eq_intro (Seq.cons (Seq.head s) (Seq.tail s)) s)

let filter_as_range (#a: Type0) (c: O.comparer a) (lo hi: Seq.seq a)
    (la ua: bool) (s: Seq.seq a) (l h: a)
  : Lemma (requires bounds lo hi la ua /\
        (la ==> Seq.index lo 0 == l) /\ (ua ==> Seq.index hi 0 == h))
      (ensures filter c lo hi la ua s == RW.filter c l h la ua s) =
  if not la && not ua then range_filter_unbounded c l h s
  else if Seq.length s = 0 then Seq.lemma_eq_intro s Seq.empty
  else (
    let l' = if Seq.length lo > 0 then Seq.index lo 0 else Seq.index s 0 in
    let h' = if Seq.length hi > 0 then Seq.index hi 0 else Seq.index s 0 in
    range_filter_bounds c l' h' l h la ua s)

let filter_cons (#a: Type0) (c: O.comparer a) (lo hi: Seq.seq a)
    (la ua: bool) (x: a) (s: Seq.seq a)
  : Lemma (requires bounds lo hi la ua)
      (ensures filter c lo hi la ua (Seq.cons x s) ==
        (if inside c lo hi la ua x then Seq.cons x (filter c lo hi la ua s)
         else filter c lo hi la ua s)) =
  let l = if Seq.length lo > 0 then Seq.index lo 0 else x in
  let h = if Seq.length hi > 0 then Seq.index hi 0 else x in
  filter_as_range c lo hi la ua (Seq.cons x s) l h;
  filter_as_range c lo hi la ua s l h;
  RW.filter_cons c l h la ua x s

let rec filter_lower (#a: Type0) (c: O.comparer a) (lo hi: Seq.seq a)
    (la ua: bool) (s: Seq.seq a) (x: a)
  : Lemma (requires bounds lo hi la ua /\
        (forall (j: nat). j < Seq.length s ==> O.compare c x (Seq.index s j) < 0))
      (ensures forall (j: nat). j < Seq.length (filter c lo hi la ua s) ==>
        O.compare c x (Seq.index (filter c lo hi la ua s) j) < 0)
      (decreases Seq.length s) =
  if Seq.length s = 0 then ()
  else (
    Seq.lemma_eq_intro (Seq.cons (Seq.head s) (Seq.tail s)) s;
    filter_cons c lo hi la ua (Seq.head s) (Seq.tail s);
    filter_lower c lo hi la ua (Seq.tail s) x;
    let at (j: nat{j < Seq.length (filter c lo hi la ua s)})
      : Lemma (O.compare c x (Seq.index (filter c lo hi la ua s) j) < 0) =
      if inside c lo hi la ua (Seq.head s) then
        (if j = 0 then () else ())
      else () in
    FStar.Classical.forall_intro at)

let rec filter_sorted (#a: Type0) (c: O.comparer a) (lo hi: Seq.seq a)
    (la ua: bool) (s: Seq.seq a)
  : Lemma (requires bounds lo hi la ua /\ S.strictly_sorted c s)
      (ensures S.strictly_sorted c (filter c lo hi la ua s))
      (decreases Seq.length s) =
  if Seq.length s = 0 then ()
  else (
    Seq.lemma_eq_intro (Seq.cons (Seq.head s) (Seq.tail s)) s;
    filter_cons c lo hi la ua (Seq.head s) (Seq.tail s);
    filter_sorted c lo hi la ua (Seq.tail s);
    filter_lower c lo hi la ua (Seq.tail s) (Seq.head s);
    let ordered (i: nat) (j: nat{i < j /\ j < Seq.length (filter c lo hi la ua s)})
      : Lemma (O.compare c (Seq.index (filter c lo hi la ua s) i)
          (Seq.index (filter c lo hi la ua s) j) < 0) =
      if inside c lo hi la ua (Seq.head s) then
        (if i = 0 then () else ())
      else () in
    introduce forall (i j: nat). i < j /\ j < Seq.length (filter c lo hi la ua s) ==>
      O.compare c (Seq.index (filter c lo hi la ua s) i)
        (Seq.index (filter c lo hi la ua s) j) < 0
    with introduce _ ==> _ with ordered i j)

let filter_append (#a: Type0) (c: O.comparer a) (lo hi: Seq.seq a)
    (la ua: bool) (s t: Seq.seq a)
  : Lemma (requires bounds lo hi la ua)
      (ensures filter c lo hi la ua (Seq.append s t) ==
        Seq.append (filter c lo hi la ua s) (filter c lo hi la ua t)) =
  if Seq.length s + Seq.length t = 0 then ()
  else (
    let both = Seq.append s t in
    let l = if Seq.length lo > 0 then Seq.index lo 0 else Seq.index both 0 in
    let h = if Seq.length hi > 0 then Seq.index hi 0 else Seq.index both 0 in
    filter_as_range c lo hi la ua both l h;
    filter_as_range c lo hi la ua s l h;
    filter_as_range c lo hi la ua t l h;
    RW.filter_append c l h la ua s t)

let filter_one (#a: Type0) (c: O.comparer a) (l h: a)
    (la ua: bool) (s: Seq.seq a)
  : Lemma (filter c (C.one l) (C.one h) la ua s == RW.filter c l h la ua s)
      [SMTPat (filter c (C.one l) (C.one h) la ua s)] =
  filter_as_range c (C.one l) (C.one h) la ua s l h

let rec filter_reverse (#a: Type0) (c: O.comparer a) (lo hi: Seq.seq a)
    (la ua: bool) (s: Seq.seq a)
  : Lemma (requires bounds lo hi la ua)
      (ensures filter c lo hi la ua (CS.reverse_all s) ==
        CS.reverse_all (filter c lo hi la ua s))
      (decreases Seq.length s) =
  if Seq.length s = 0 then (
    Seq.lemma_eq_intro s Seq.empty;
    Seq.lemma_eq_intro (CS.reverse_all s) Seq.empty)
  else (
    let x = Seq.head s in
    let rest = Seq.tail s in
    Seq.lemma_eq_intro s (Seq.cons x rest);
    Seq.lemma_eq_intro (CS.reverse_all s)
      (Seq.append (CS.reverse_all rest) (Seq.cons x Seq.empty));
    filter_reverse c lo hi la ua rest;
    filter_append c lo hi la ua (CS.reverse_all rest) (Seq.cons x Seq.empty);
    filter_cons c lo hi la ua x Seq.empty;
    filter_cons c lo hi la ua x rest;
    if inside c lo hi la ua x then
      Seq.lemma_eq_intro (CS.reverse_all (Seq.cons x (filter c lo hi la ua rest)))
        (Seq.append (CS.reverse_all (filter c lo hi la ua rest)) (Seq.cons x Seq.empty))
    else Seq.lemma_eq_intro
      (Seq.append (CS.reverse_all (filter c lo hi la ua rest)) Seq.empty)
      (CS.reverse_all (filter c lo hi la ua rest)))

let initial (#a: Type0) (c: O.comparer a) (lo hi: Seq.seq a)
    (la ua rev: bool) (t: T.tree (a & bool))
  : Lemma (requires bounds lo hi la ua)
      (ensures filter c lo hi la ua (Walk.okeys rev t) ==
        (if rev then CS.reverse_all (filter c lo hi la ua (ST.keys t))
         else filter c lo hi la ua (ST.keys t))) =
  if rev then (
    Walk.okeys_rev t;
    filter_reverse c lo hi la ua (ST.keys t))
  else Walk.okeys_fwd t

let walkable_push (#a: Type0) (c: O.comparer a) (lo hi: Seq.seq a)
    (la ua: bool) (h: Q.observation a) (s: Seq.seq (N.class_Node__opt a))
    (x: N.class_Node__opt a)
  : Lemma (requires walkable c lo hi la ua h s /\ Q.wf h x /\ not (B.is_null x) /\
        inside c lo hi la ua (Own.item (Q.get h x)) /\
        (la || ua ==> S.strictly_sorted c (ST.keys (Q.tree_at h x))))
      (ensures walkable c lo hi la ua h (Seq.snoc s x)) =
  F.step h x;
  let at (i: nat)
    : Lemma (i < Seq.length (Seq.snoc s x) ==>
        (Q.wf h (Seq.index (Seq.snoc s x) i) /\ not (B.is_null (Seq.index (Seq.snoc s x) i)) /\
        (not la && not ua \/
         (inside c lo hi la ua (Own.item (Q.get h (Seq.index (Seq.snoc s x) i))) /\
          S.strictly_sorted c (ST.keys (Q.tree_at h (Seq.index (Seq.snoc s x) i))))))) =
    if i < Seq.length s then
      assert (Seq.index (Seq.snoc s x) i == Seq.index s i)
    else () in
  FStar.Classical.forall_intro at

let pop_at (#a: Type0) (c: O.comparer a) (lo hi: Seq.seq a)
    (la ua rev: bool) (h: Q.observation a) (s: Seq.seq (N.class_Node__opt a))
    (ks: Seq.seq a) (offset: int)
  : Lemma (requires bounds lo hi la ua /\ Seq.length s > 0 /\
        walkable c lo hi la ua h s /\ 0 <= offset /\ offset <= Seq.length ks /\
        filter c lo hi la ua (Q.pending rev h s) == Seq.slice ks offset (Seq.length ks))
      (ensures (
        let n = Seq.length s - 1 in
        let x = Seq.index s n in
        let tail = Seq.slice s 0 n in
        let rest = Seq.append (Walk.okeys rev (Q.tree_at h (F.far rev h x))) (Q.pending rev h tail) in
        Q.mem h x /\ not (B.is_null x) /\ Q.wf h x /\ offset < Seq.length ks /\
        walkable c lo hi la ua h tail /\ Q.wf h (F.far rev h x) /\
        (la || ua ==> S.strictly_sorted c (ST.keys (Q.tree_at h x))) /\
        Own.item (Q.get h x) == Seq.index ks offset /\
        ST.root_key (Q.tree_at h x) (Seq.index ks offset) == Seq.index ks offset /\
        Seq.length rest < Seq.length (Q.pending rev h s) /\
        filter c lo hi la ua rest == Seq.slice ks (offset + 1) (Seq.length ks))) =
  W.pop rev h s;
  let n = Seq.length s - 1 in
  let x = Seq.index s n in
  let tail = Seq.slice s 0 n in
  F.step h x;
  let rest = Seq.append (Walk.okeys rev (Q.tree_at h (F.far rev h x))) (Q.pending rev h tail) in
  let k = Own.item (Q.get h x) in
  assert (inside c lo hi la ua k);
  filter_cons c lo hi la ua k rest;
  assert (forall (i: nat). i < n ==> Seq.index tail i == Seq.index s i);
  RW.cons_window k (filter c lo hi la ua rest) ks offset

let filter_none (#a: Type0) (c: O.comparer a) (lo hi: Seq.seq a)
    (la ua: bool) (s: Seq.seq a)
  : Lemma (requires bounds lo hi la ua /\
        (forall (i: nat). i < Seq.length s ==> not (inside c lo hi la ua (Seq.index s i))))
      (ensures filter c lo hi la ua s == Seq.empty) =
  if Seq.length s = 0 then Seq.lemma_eq_intro s Seq.empty
  else (
    let l = if Seq.length lo > 0 then Seq.index lo 0 else Seq.index s 0 in
    let h = if Seq.length hi > 0 then Seq.index hi 0 else Seq.index s 0 in
    filter_as_range c lo hi la ua s l h;
    RW.filter_none c l h la ua s)

let skip_below (#a #tag: Type0) (c: O.comparer a) (lo hi: Seq.seq a)
    (la ua rev: bool) (l: T.tree (a & tag)) (k: a) (g: tag)
    (r: T.tree (a & tag)) (rest: Seq.seq a)
  : Lemma (requires bounds lo hi la ua /\ la /\ O.compare c (Seq.index lo 0) k > 0 /\
        S.strictly_sorted c (ST.keys (T.Branch l (k, g) r)))
      (ensures filter c lo hi la ua (Seq.append (Walk.okeys rev (T.Branch l (k, g) r)) rest) ==
        filter c lo hi la ua (Seq.append (Walk.okeys rev r) rest)) =
  ST.sorted_branch c l k g r;
  let left = Walk.okeys rev l in
  let right = Walk.okeys rev r in
  let at (i: nat)
    : Lemma (i < Seq.length left ==> not (inside c lo hi la ua (Seq.index left i))) =
    if i < Seq.length left then (
      let j = if rev then Seq.length (ST.keys l) - 1 - i else i in
      O.compare_trans c (Seq.index (ST.keys l) j) k (Seq.index lo 0))
    else () in
  FStar.Classical.forall_intro at;
  filter_none c lo hi la ua left;
  if rev then (
    filter_append c lo hi la ua right (Seq.cons k left);
    filter_cons c lo hi la ua k left;
    Seq.append_empty_r (filter c lo hi la ua right))
  else (
    filter_append c lo hi la ua left (Seq.cons k right);
    filter_cons c lo hi la ua k right;
    Seq.append_empty_l (filter c lo hi la ua right));
  filter_append c lo hi la ua (Walk.okeys rev (T.Branch l (k, g) r)) rest;
  filter_append c lo hi la ua right rest

let skip_above (#a #tag: Type0) (c: O.comparer a) (lo hi: Seq.seq a)
    (la ua rev: bool) (l: T.tree (a & tag)) (k: a) (g: tag)
    (r: T.tree (a & tag)) (rest: Seq.seq a)
  : Lemma (requires bounds lo hi la ua /\ ua /\ O.compare c k (Seq.index hi 0) > 0 /\
        S.strictly_sorted c (ST.keys (T.Branch l (k, g) r)))
      (ensures filter c lo hi la ua (Seq.append (Walk.okeys rev (T.Branch l (k, g) r)) rest) ==
        filter c lo hi la ua (Seq.append (Walk.okeys rev l) rest)) =
  ST.sorted_branch c l k g r;
  let left = Walk.okeys rev l in
  let right = Walk.okeys rev r in
  let at (i: nat)
    : Lemma (i < Seq.length right ==> not (inside c lo hi la ua (Seq.index right i))) =
    if i < Seq.length right then (
      let j = if rev then Seq.length (ST.keys r) - 1 - i else i in
      O.compare_trans c (Seq.index hi 0) k (Seq.index (ST.keys r) j))
    else () in
  FStar.Classical.forall_intro at;
  filter_none c lo hi la ua right;
  if rev then (
    filter_append c lo hi la ua right (Seq.cons k left);
    filter_cons c lo hi la ua k left;
    Seq.append_empty_l (filter c lo hi la ua left))
  else (
    filter_append c lo hi la ua left (Seq.cons k right);
    filter_cons c lo hi la ua k right;
    Seq.append_empty_r (filter c lo hi la ua left));
  filter_append c lo hi la ua (Walk.okeys rev (T.Branch l (k, g) r)) rest;
  filter_append c lo hi la ua left rest

let skip (#a: Type0) (c: O.comparer a) (lo hi: Seq.seq a)
    (la ua rev: bool) (h: Q.observation a) (x child: N.class_Node__opt a)
    (rest: Seq.seq a)
  : Lemma (requires bounds lo hi la ua /\ Q.wf h x /\ not (B.is_null x) /\
        S.strictly_sorted c (ST.keys (Q.tree_at h x)) /\
        ((la /\ O.compare c (Seq.index lo 0) (Own.item (Q.get h x)) > 0 /\
          child == Own.right (Q.get h x)) \/
         (ua /\ O.compare c (Own.item (Q.get h x)) (Seq.index hi 0) > 0 /\
          child == Own.left (Q.get h x))))
      (ensures Q.wf h child /\ S.strictly_sorted c (ST.keys (Q.tree_at h child)) /\
        T.size (Q.tree_at h child) < T.size (Q.tree_at h x) /\
        filter c lo hi la ua (Seq.append (Walk.okeys rev (Q.tree_at h x)) rest) ==
        filter c lo hi la ua (Seq.append (Walk.okeys rev (Q.tree_at h child)) rest)) =
  F.step h x;
  F.children rev h x;
  let T.Branch l (k, g) r = Q.tree_at h x in
  ST.sorted_branch c l k g r;
  if la && O.compare c (Seq.index lo 0) k > 0 &&
      Pulse.Lib.CSharp.RefEq.ref_eq child (Own.right (Q.get h x)) then
    skip_below c lo hi la ua rev l k g r rest
  else
    skip_above c lo hi la ua rev l k g r rest

let side (#a: Type0) (c: O.comparer a) (bound: Seq.seq a)
    (active upper: bool) (keys: Seq.seq a) : prop =
  active ==> Seq.length bound > 0 /\
    (forall (i: nat). i < Seq.length keys ==>
      (if upper then O.compare c (Seq.index keys i) (Seq.index bound 0) <= 0
       else O.compare c (Seq.index bound 0) (Seq.index keys i) <= 0))

let side_branch (#a #tag: Type0) (c: O.comparer a) (bound: Seq.seq a)
    (active upper: bool) (l: T.tree (a & tag)) (k: a) (g: tag) (r: T.tree (a & tag))
  : Lemma (requires side c bound active upper (ST.keys (T.Branch l (k, g) r)))
      (ensures side c bound active upper (ST.keys l) /\
        side c bound active upper (Seq.cons k Seq.empty) /\
        side c bound active upper (ST.keys r)) =
  let all = ST.keys (T.Branch l (k, g) r) in
  let at_left (i: nat) : Lemma (i < Seq.length (ST.keys l) ==>
      Seq.index (ST.keys l) i == Seq.index all i) = () in
  let at_right (i: nat) : Lemma (i < Seq.length (ST.keys r) ==>
      Seq.index (ST.keys r) i == Seq.index all (Seq.length (ST.keys l) + 1 + i)) = () in
  FStar.Classical.forall_intro at_left;
  FStar.Classical.forall_intro at_right;
  assert (Seq.index all (Seq.length (ST.keys l)) == k)

let side_from_root (#a #tag: Type0) (c: O.comparer a) (bound: Seq.seq a)
    (active upper: bool) (l: T.tree (a & tag)) (k: a) (g: tag) (r: T.tree (a & tag))
  : Lemma (requires S.strictly_sorted c (ST.keys (T.Branch l (k, g) r)) /\
        side c bound active upper (Seq.cons k Seq.empty))
      (ensures side c bound active upper (ST.keys (if upper then l else r))) =
  ST.sorted_branch c l k g r;
  let keys = ST.keys (if upper then l else r) in
  let at (i: nat)
    : Lemma (active /\ i < Seq.length keys ==>
        (if upper then O.compare c (Seq.index keys i) (Seq.index bound 0) <= 0
         else O.compare c (Seq.index bound 0) (Seq.index keys i) <= 0)) =
    if active && i < Seq.length keys then (
      if upper then O.compare_trans c (Seq.index keys i) k (Seq.index bound 0)
      else O.compare_trans c (Seq.index bound 0) k (Seq.index keys i))
    else () in
  FStar.Classical.forall_intro at

// Initialization approaches the lower bound in forward order and the upper
// bound in reverse order. After a pop, the successor subtree has the dual bound.
let frontier (#a #tag: Type0) (c: O.comparer a) (lo hi: Seq.seq a)
    (la ua upper: bool) (t: T.tree (a & tag)) : prop =
  (la || ua) ==>
  S.strictly_sorted c (ST.keys t) /\
  (match t with
   | T.Leaf -> True
   | T.Branch _ (k, _) _ ->
     inside c lo hi la ua k \/
       side c (if upper then hi else lo) (if upper then ua else la) upper (ST.keys t))

let frontier_push (#a #tag: Type0) (c: O.comparer a) (lo hi: Seq.seq a)
    (la ua upper: bool) (l: T.tree (a & tag)) (k: a) (g: tag) (r: T.tree (a & tag))
  : Lemma (requires bounds lo hi la ua /\ S.strictly_sorted c (ST.keys (T.Branch l (k, g) r)) /\
        inside c lo hi la ua k)
      (ensures frontier c lo hi la ua upper (if upper then l else r)) =
  ST.sorted_branch c l k g r;
  side_from_root c (if upper then hi else lo) (if upper then ua else la) upper l k g r

let frontier_outside (#a #tag: Type0) (c: O.comparer a) (lo hi: Seq.seq a)
    (la ua upper: bool) (l: T.tree (a & tag)) (k: a) (g: tag) (r: T.tree (a & tag))
  : Lemma (requires bounds lo hi la ua /\ frontier c lo hi la ua upper (T.Branch l (k, g) r) /\
        not (inside c lo hi la ua k))
      (ensures frontier c lo hi la ua upper l /\ frontier c lo hi la ua upper r /\
        (if upper then la /\ O.compare c (Seq.index lo 0) k > 0
         else ua /\ O.compare c k (Seq.index hi 0) > 0)) =
  ST.sorted_branch c l k g r;
  side_branch c (if upper then hi else lo) (if upper then ua else la) upper l k g r

let frontier_step (#a: Type0) (c: O.comparer a) (lo hi: Seq.seq a)
    (la ua upper: bool) (h: Q.observation a) (x: N.class_Node__opt a)
  : Lemma (requires bounds lo hi la ua /\ Q.wf h x /\ not (B.is_null x) /\
        frontier c lo hi la ua upper (Q.tree_at h x))
      (ensures Q.mem h x /\
        (let v = Q.get h x in
         Q.wf h (Own.left v) /\ Q.wf h (Own.right v) /\
         (inside c lo hi la ua (Own.item v) ==>
           frontier c lo hi la ua upper (Q.tree_at h (if upper then Own.left v else Own.right v))) /\
         (not (inside c lo hi la ua (Own.item v)) ==>
           frontier c lo hi la ua upper (Q.tree_at h (Own.left v)) /\
           frontier c lo hi la ua upper (Q.tree_at h (Own.right v)) /\
           (if upper then la /\ O.compare c (Seq.index lo 0) (Own.item v) > 0
            else ua /\ O.compare c (Own.item v) (Seq.index hi 0) > 0)))) =
  F.step h x;
  if not la && not ua then ()
  else (
    let T.Branch l (k, g) r = Q.tree_at h x in
    if (not la || O.compare c (Seq.index lo 0) k <= 0) &&
        (not ua || O.compare c k (Seq.index hi 0) <= 0) then
      frontier_push c lo hi la ua upper l k g r
    else
      frontier_outside c lo hi la ua upper l k g r)

let ordered_children (#a: Type0) (c: O.comparer a) (h: Q.observation a)
    (x: N.class_Node__opt a)
  : Lemma (requires Q.wf h x /\ not (B.is_null x) /\ S.strictly_sorted c (ST.keys (Q.tree_at h x)))
      (ensures Q.mem h x /\
        (let v = Q.get h x in
         Q.wf h (Own.left v) /\ Q.wf h (Own.right v) /\
         (not (B.is_null (Own.left v)) ==> Q.mem h (Own.left v) /\
           O.compare c (Own.item (Q.get h (Own.left v))) (Own.item v) < 0) /\
         (not (B.is_null (Own.right v)) ==> Q.mem h (Own.right v) /\
           O.compare c (Own.item v) (Own.item (Q.get h (Own.right v))) < 0))) =
  F.step h x;
  let v = Q.get h x in
  let T.Branch l (k, g) r = Q.tree_at h x in
  ST.sorted_branch c l k g r;
  if not (B.is_null (Own.left v)) then (
    F.step h (Own.left v);
    let T.Branch ll (lk, _) lr = l in
    assert (Seq.index (ST.keys l) (Seq.length (ST.keys ll)) == lk))
  else ();
  if not (B.is_null (Own.right v)) then (
    F.step h (Own.right v);
    let T.Branch rl (rk, _) rr = r in
    assert (Seq.index (ST.keys r) (Seq.length (ST.keys rl)) == rk))
  else ()

let excluded_children (#a: Type0) (c: O.comparer a) (lo hi: Seq.seq a)
    (la ua: bool) (h: Q.observation a) (x: N.class_Node__opt a)
  : Lemma (requires bounds lo hi la ua /\ Q.wf h x /\ not (B.is_null x) /\
        (la || ua ==> S.strictly_sorted c (ST.keys (Q.tree_at h x))))
      (ensures Q.mem h x /\
        (let v = Q.get h x in
         (la /\ O.compare c (Seq.index lo 0) (Own.item v) > 0 /\ not (B.is_null (Own.left v)) ==>
           Q.mem h (Own.left v) /\ not (inside c lo hi la ua (Own.item (Q.get h (Own.left v))))) /\
         (ua /\ O.compare c (Own.item v) (Seq.index hi 0) > 0 /\ not (B.is_null (Own.right v)) ==>
           Q.mem h (Own.right v) /\ not (inside c lo hi la ua (Own.item (Q.get h (Own.right v))))))) =
  F.step h x;
  if la || ua then (
    ordered_children c h x;
    let v = Q.get h x in
    if la && O.compare c (Seq.index lo 0) (Own.item v) > 0 && not (B.is_null (Own.left v)) then
      O.compare_trans c (Own.item (Q.get h (Own.left v))) (Own.item v) (Seq.index lo 0)
    else ();
    if ua && O.compare c (Own.item v) (Seq.index hi 0) > 0 && not (B.is_null (Own.right v)) then
      O.compare_trans c (Seq.index hi 0) (Own.item v) (Own.item (Q.get h (Own.right v)))
    else ())
  else ()

let successor (#a #tag: Type0) (c: O.comparer a) (lo hi: Seq.seq a)
    (la ua upper: bool) (t: T.tree (a & tag)) : prop =
  if not la && not ua then True
  else S.strictly_sorted c (ST.keys t) /\
    side c (if upper then hi else lo) (if upper then ua else la) upper (ST.keys t)

let successor_step (#a: Type0) (c: O.comparer a) (lo hi: Seq.seq a)
    (la ua upper: bool) (h: Q.observation a) (x: N.class_Node__opt a)
  : Lemma (requires bounds lo hi la ua /\ Q.wf h x /\ not (B.is_null x) /\
        successor c lo hi la ua upper (Q.tree_at h x))
      (ensures Q.mem h x /\
        (let v = Q.get h x in
         Q.wf h (Own.left v) /\ Q.wf h (Own.right v) /\
         successor c lo hi la ua upper (Q.tree_at h (Own.left v)) /\
         successor c lo hi la ua upper (Q.tree_at h (Own.right v)) /\
         (not (inside c lo hi la ua (Own.item v)) ==>
           (if upper then la /\ O.compare c (Seq.index lo 0) (Own.item v) > 0
            else ua /\ O.compare c (Own.item v) (Seq.index hi 0) > 0)))) =
  F.step h x;
  if not la && not ua then ()
  else (
    let T.Branch l (k, g) r = Q.tree_at h x in
    ST.sorted_branch c l k g r;
    side_branch c (if upper then hi else lo) (if upper then ua else la) upper l k g r)

let pop_frontier (#a: Type0) (c: O.comparer a) (lo hi: Seq.seq a)
    (la ua rev: bool) (h: Q.observation a) (s: Seq.seq (N.class_Node__opt a))
  : Lemma (requires bounds lo hi la ua /\ Seq.length s > 0 /\ walkable c lo hi la ua h s)
      (ensures successor c lo hi la ua rev (Q.tree_at h (F.far rev h (Seq.index s (Seq.length s - 1))))) =
  if not la && not ua then ()
  else (
    W.pop rev h s;
    let x = Seq.index s (Seq.length s - 1) in
    F.step h x;
    F.children rev h x;
    let T.Branch l (k, g) r = Q.tree_at h x in
    ST.sorted_branch c l k g r;
    side_from_root c (if rev then hi else lo) (if rev then ua else la) rev l k g r)

let rec root_facts (#a #tag: Type0) (c: O.comparer a) (lo hi: Seq.seq a)
    (la ua rev upper: bool) (t: T.tree (a & tag))
  : Lemma (requires bounds lo hi la ua /\ S.strictly_sorted c (ST.keys t))
      (ensures (
        let rt = C.root_s c t lo hi la ua in
        frontier c lo hi la ua upper rt /\ T.size rt <= T.size t /\
        filter c lo hi la ua (Walk.okeys rev rt) == filter c lo hi la ua (Walk.okeys rev t)))
      (decreases t) =
  if not la && not ua then ()
  else match t with
    | T.Leaf -> ()
    | T.Branch l (k, g) r ->
      ST.sorted_branch c l k g r;
      if la && O.compare c (Seq.index lo 0) k > 0 then (
        root_facts c lo hi la ua rev upper r;
        skip_below c lo hi la ua rev l k g r Seq.empty;
        Seq.append_empty_r (Walk.okeys rev t);
        Seq.append_empty_r (Walk.okeys rev r))
      else if ua && O.compare c k (Seq.index hi 0) > 0 then (
        root_facts c lo hi la ua rev upper l;
        skip_above c lo hi la ua rev l k g r Seq.empty;
        Seq.append_empty_r (Walk.okeys rev t);
        Seq.append_empty_r (Walk.okeys rev l))
      else ()

let start (#a #tag: Type0) (c: O.comparer a) (lo hi: Seq.seq a)
    (la ua rev upper: bool) (t: T.tree (a & tag)) (rest: Seq.seq a)
  : Lemma (requires bounds lo hi la ua /\ S.strictly_sorted c (ST.keys t) /\ Seq.length rest == 0)
      (ensures (
        let rt = C.root_s c t lo hi la ua in
        frontier c lo hi la ua upper rt /\ T.size rt <= T.size t /\
        filter c lo hi la ua (Seq.append (Walk.okeys rev rt) rest) ==
          filter c lo hi la ua (Walk.okeys rev t))) =
  root_facts c lo hi la ua rev upper t;
  Seq.lemma_eq_intro rest Seq.empty;
  Seq.append_empty_r (Walk.okeys rev (C.root_s c t lo hi la ua))
