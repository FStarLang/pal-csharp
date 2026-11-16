module Pulse.Lib.CSharp.RangeWalk

/// R35.14. A range-pruned in-order walk of a region's search tree: `SortedSet<T>.TreeSubSet`'s
/// `InOrderTreeWalk`. It is R27.35's walk (`RegionWalk`) over a stack of pointers into the
/// region, except that a node outside the range is not pushed: the walk moves to the side
/// of it where the range is. What the walk visits is therefore the in-range keys
/// (`filter`) of what the plain walk would.
///
/// * `filter c lo hi la ua s`: the items of `s` within the active bounds, in order.
/// * `rwalkable h s`: every pointer on the stack holds an in-range key, and the subtree
///   below it is strictly sorted. A walk keeps both, since it pushes only in-range nodes
///   and descends only into subtrees of a sorted tree.
/// * `skip_right`/`skip_left`: a node below (above) the range, and its whole left (right)
///   side, is out of range, so moving to its right (left) child keeps the in-range keys.
/// * `range_root_filter`: the view's root (`SearchTree.range_root`) holds all the in-range
///   keys of the whole tree.
/// * The breadth-first walk (`BreadthFirstTreeWalk`), R27.40's over a queue of pointers:
///   `rqueue` (every queued pointer is over a strictly sorted subtree), `rbf_next` (the
///   queue after a round, which queues a child only if the range may reach into it),
///   `rbf_start` and `rbf_dequeue`. A pruned child's subtree has no in-range key
///   (`rbf_prune`), so the walk calls back on exactly the in-range keys of R27.40's walk.
/// * R35.17. The view's `MinInternal`/`MaxInternal`, a descent from the view's root:
///   `first_or`/`last_or`, the steps `min_step`/`max_step`, and `min_max_goal`, which says
///   the descent's target in the root's subtree is the least (greatest) in-range key.
/// * R35.19. The view's re-count, a walk whose callback always returns true: `all_true`
///   (every call in a trace returned true), kept by such a call (`all_true_snoc`); a walk
///   whose calls all returned true called back on every key (`counted`).
///
/// Every region definition takes the region class's view and links first (`[RegionOp]`,
/// R27.22). Nothing here is trusted: it is proved from `Region`, `RegionWalk`,
/// `SearchTree` and `Order`.

open Pulse.Lib.CSharp.Region
module B = Pulse.Lib.Box
module T = Pulse.Lib.CSharp.Tree
module O = Pulse.Lib.CSharp.Order
module S = Pulse.Lib.CSharp.Sorted
module ST = Pulse.Lib.CSharp.SearchTree
module RW = Pulse.Lib.CSharp.RegionWalk
module Seq = FStar.Seq
module I32 = FStar.Int32
module SF = Pulse.Lib.CSharp.SetFilter

let rec filter (#a: Type0) (c: O.comparer a) (lo hi: a) (la ua: bool) (s: Seq.seq a)
  : Tot (Seq.seq a) (decreases Seq.length s) =
  if Seq.length s = 0 then Seq.empty
  else
    let t = filter c lo hi la ua (Seq.tail s) in
    if ST.in_range c lo hi la ua (Seq.head s) then Seq.cons (Seq.head s) t else t

let filter_empty (#a: Type0) (c: O.comparer a) (lo hi: a) (la ua: bool)
  : Lemma (filter c lo hi la ua Seq.empty == Seq.empty)
          [SMTPat (filter c lo hi la ua Seq.empty)]
  = ()

let filter_cons (#a: Type0) (c: O.comparer a) (lo hi: a) (la ua: bool) (x: a) (s: Seq.seq a)
  : Lemma (filter c lo hi la ua (Seq.cons x s) ==
           (if ST.in_range c lo hi la ua x then Seq.cons x (filter c lo hi la ua s)
            else filter c lo hi la ua s))
          [SMTPat (filter c lo hi la ua (Seq.cons x s))]
  = Seq.lemma_tl x s

let rec filter_append (#a: Type0) (c: O.comparer a) (lo hi: a) (la ua: bool) (s t: Seq.seq a)
  : Lemma (ensures filter c lo hi la ua (Seq.append s t) ==
                   Seq.append (filter c lo hi la ua s) (filter c lo hi la ua t))
          (decreases Seq.length s)
          [SMTPat (filter c lo hi la ua (Seq.append s t))]
  = if Seq.length s = 0 then begin
      Seq.lemma_eq_intro (Seq.append s t) t;
      Seq.lemma_eq_intro (Seq.append (filter c lo hi la ua s) (filter c lo hi la ua t))
                         (filter c lo hi la ua t)
    end
    else begin
      let x = Seq.head s in
      let s' = Seq.tail s in
      Seq.lemma_eq_intro (Seq.append s t) (Seq.cons x (Seq.append s' t));
      Seq.lemma_eq_intro s (Seq.cons x s');
      filter_cons c lo hi la ua x (Seq.append s' t);
      filter_cons c lo hi la ua x s';
      filter_append c lo hi la ua s' t;
      if ST.in_range c lo hi la ua x then
        Seq.lemma_eq_intro (Seq.cons x (Seq.append (filter c lo hi la ua s') (filter c lo hi la ua t)))
                           (Seq.append (Seq.cons x (filter c lo hi la ua s')) (filter c lo hi la ua t))
      else ()
    end

/// A filter is no longer than what it filters.
let rec filter_length (#a: Type0) (c: O.comparer a) (lo hi: a) (la ua: bool) (s: Seq.seq a)
  : Lemma (ensures Seq.length (filter c lo hi la ua s) <= Seq.length s)
          (decreases Seq.length s)
          [SMTPat (Seq.length (filter c lo hi la ua s))]
  = if Seq.length s = 0 then () else filter_length c lo hi la ua (Seq.tail s)

/// A sequence none of whose items is in range filters to nothing.
let rec filter_none (#a: Type0) (c: O.comparer a) (lo hi: a) (la ua: bool) (s: Seq.seq a)
  : Lemma (requires forall (i: nat). i < Seq.length s ==> not (ST.in_range c lo hi la ua (Seq.index s i)))
          (ensures filter c lo hi la ua s == Seq.empty)
          (decreases Seq.length s)
  = if Seq.length s = 0 then ()
    else begin
      assert (forall (i: nat). i < Seq.length (Seq.tail s) ==> Seq.index (Seq.tail s) i == Seq.index s (i + 1));
      filter_none c lo hi la ua (Seq.tail s)
    end

/// Below the range: a node whose key is under an active lower bound, and everything left
/// of it, is out of range in a sorted tree.
let skip_below (#a #b: Type0) (c: O.comparer a) (lo hi: a) (la ua: bool)
    (l: T.tree (a & b)) (k: a) (g: b) (r: T.tree (a & b)) (rest: Seq.seq a)
  : Lemma (requires S.strictly_sorted c (ST.keys (T.Branch l (k, g) r)) /\ la /\ O.compare c lo k > 0)
          (ensures filter c lo hi la ua (Seq.append (ST.keys (T.Branch l (k, g) r)) rest) ==
                   filter c lo hi la ua (Seq.append (ST.keys r) rest))
  = ST.sorted_branch c l k g r;
    let sl = ST.keys l in
    let out (i: nat) : Lemma (i < Seq.length sl ==> not (ST.in_range c lo hi la ua (Seq.index sl i)))
      = if i < Seq.length sl then O.compare_trans c (Seq.index sl i) k lo else ()
    in
    FStar.Classical.forall_intro out;
    filter_none c lo hi la ua sl;
    Seq.append_assoc sl (Seq.cons k (ST.keys r)) rest;
    Seq.lemma_eq_intro (Seq.append (Seq.cons k (ST.keys r)) rest) (Seq.cons k (Seq.append (ST.keys r) rest));
    filter_append c lo hi la ua sl (Seq.append (Seq.cons k (ST.keys r)) rest);
    filter_cons c lo hi la ua k (Seq.append (ST.keys r) rest);
    Seq.append_empty_l (filter c lo hi la ua (Seq.append (Seq.cons k (ST.keys r)) rest))

let skip_above (#a #b: Type0) (c: O.comparer a) (lo hi: a) (la ua: bool)
    (l: T.tree (a & b)) (k: a) (g: b) (r: T.tree (a & b)) (rest: Seq.seq a)
  : Lemma (requires S.strictly_sorted c (ST.keys (T.Branch l (k, g) r)) /\
                    not (ST.in_range c lo hi la ua k) /\ not (la && O.compare c lo k > 0))
          (ensures filter c lo hi la ua (Seq.append (ST.keys (T.Branch l (k, g) r)) rest) ==
                   filter c lo hi la ua (Seq.append (ST.keys l) rest))
  = ST.sorted_branch c l k g r;
    let sr = ST.keys r in
    let out (i: nat) : Lemma (i < Seq.length sr ==> not (ST.in_range c lo hi la ua (Seq.index sr i)))
      = if i < Seq.length sr then O.compare_trans c hi k (Seq.index sr i) else ()
    in
    FStar.Classical.forall_intro out;
    filter_none c lo hi la ua sr;
    let sl = ST.keys l in
    Seq.append_assoc sl (Seq.cons k sr) rest;
    Seq.lemma_eq_intro (Seq.append (Seq.cons k sr) rest) (Seq.cons k (Seq.append sr rest));
    filter_append c lo hi la ua sl (Seq.append (Seq.cons k sr) rest);
    filter_cons c lo hi la ua k (Seq.append sr rest);
    filter_append c lo hi la ua sr rest;
    Seq.append_empty_l (filter c lo hi la ua rest);
    filter_append c lo hi la ua sl rest

/// R32.14's view root holds every in-range key of the tree, and is a sorted subtree of it.
let rec range_root_filter (#a #b: Type0) (c: O.comparer a) (t: T.tree (a & b)) (lo hi: a) (la ua: bool)
  : Lemma (requires S.strictly_sorted c (ST.keys t))
          (ensures filter c lo hi la ua (ST.keys (ST.range_root c t lo hi la ua)) == filter c lo hi la ua (ST.keys t) /\
                   S.strictly_sorted c (ST.keys (ST.range_root c t lo hi la ua)) /\
                   T.size (ST.range_root c t lo hi la ua) <= T.size t)
          (decreases t)
  = match t with
    | T.Leaf -> ()
    | T.Branch l (v, g) r ->
      ST.sorted_branch c l v g r;
      if la && O.compare c lo v > 0 then begin
        range_root_filter c r lo hi la ua;
        skip_below c lo hi la ua l v g r Seq.empty;
        Seq.append_empty_r (ST.keys t);
        Seq.append_empty_r (ST.keys r)
      end
      else if ua && O.compare c hi v < 0 then begin
        range_root_filter c l lo hi la ua;
        skip_above c lo hi la ua l v g r Seq.empty;
        Seq.append_empty_r (ST.keys t);
        Seq.append_empty_r (ST.keys l)
      end
      else ()

(* ---------------------------------------------------------------------------------- *)
(* The walk over the region.                                                           *)

let key_at (#r #a #b: Type0) (view: B.box r -> r -> (a & b)) (h: heap r) (x: B.box r { mem h x }) : a =
  fst (view x (get h x))

/// Every pointer on the stack holds an in-range key over a strictly sorted subtree.
let rwalkable (#r #a #b: Type0) (view: B.box r -> r -> (a & b)) (left right: r -> B.box r)
    (h: heap r) (c: O.comparer a) (lo hi: a) (la ua: bool) (s: Seq.seq (B.box r)) : prop =
  forall (i: nat). {:pattern Seq.index s i} i < Seq.length s ==>
    (mem h (Seq.index s i) /\
     ST.in_range c lo hi la ua (key_at view h (Seq.index s i)) /\
     S.strictly_sorted c (ST.keys (tree_of view left right h (Seq.index s i))))

let rwalkable_empty (#r #a #b: Type0) (view: B.box r -> r -> (a & b)) (left right: r -> B.box r)
    (h: heap r) (c: O.comparer a) (lo hi: a) (la ua: bool) (s: Seq.seq (B.box r))
  : Lemma (requires Seq.length s == 0)
          (ensures rwalkable view left right h c lo hi la ua s /\
                   RW.walkable view left right h s /\
                   RW.pending view left right false h s == Seq.empty)
  = ()

/// Pushing an in-range node over a sorted subtree keeps the stack range-walkable.
let push (#r #a #b: Type0) (view: B.box r -> r -> (a & b)) (left right: r -> B.box r)
    (h: heap r) (c: O.comparer a) (lo hi: a) (la ua: bool) (s: Seq.seq (B.box r)) (x: B.box r)
  : Lemma (requires rwalkable view left right h c lo hi la ua s /\
                    wf left right h x /\ not (B.is_null x) /\
                    ST.in_range c lo hi la ua (fst (view x (get h x))) /\
                    S.strictly_sorted c (ST.keys (tree_of view left right h x)))
          (ensures rwalkable view left right h c lo hi la ua (Seq.snoc s x) /\
                   S.strictly_sorted c (ST.keys (tree_of view left right h (left (get h x)))))
  = wf_step view left right h x;
    let T.Branch l (k, g) rt = tree_of view left right h x in
    ST.sorted_branch c l k g rt;
    let s' = Seq.snoc s x in
    assert (forall (i: nat). i < Seq.length s ==> Seq.index s' i == Seq.index s i);
    assert (Seq.index s' (Seq.length s) == x)

/// The descent at a node under an active lower bound: its key and its left side are out of
/// range, so the walk moves right. The bound is tested as the code tests it, on the `int`
/// `compare_i32` gives, so that the branch's own condition is what the lemma needs.
let skip_right (#r #a #b: Type0) (view: B.box r -> r -> (a & b)) (left right: r -> B.box r)
    (h: heap r) (c: O.comparer a) (lo hi: a) (la ua: bool) (x: B.box r) (rest: Seq.seq a)
  : Lemma (requires wf left right h x /\ not (B.is_null x) /\
                    la /\ I32.v (S.compare_i32 c lo (fst (view x (get h x)))) > 0 /\
                    S.strictly_sorted c (ST.keys (tree_of view left right h x)))
          (ensures wf left right h (right (get h x)) /\
                   S.strictly_sorted c (ST.keys (tree_of view left right h (right (get h x)))) /\
                   T.size (tree_of view left right h (right (get h x))) < T.size (tree_of view left right h x) /\
                   filter c lo hi la ua (Seq.append (RW.okeys false (tree_of view left right h x)) rest) ==
                   filter c lo hi la ua (Seq.append (RW.okeys false (tree_of view left right h (right (get h x)))) rest))
  = wf_step view left right h x;
    let T.Branch l (k, g) rt = tree_of view left right h x in
    ST.sorted_branch c l k g rt;
    RW.okeys_fwd (tree_of view left right h x);
    RW.okeys_fwd rt;
    skip_below c lo hi la ua l k g rt rest

/// The descent at a node outside the range and not under its lower bound: it is over the
/// upper bound, as is its right side, so the walk moves left.
let skip_left (#r #a #b: Type0) (view: B.box r -> r -> (a & b)) (left right: r -> B.box r)
    (h: heap r) (c: O.comparer a) (lo hi: a) (la ua: bool) (x: B.box r) (rest: Seq.seq a)
  : Lemma (requires wf left right h x /\ not (B.is_null x) /\
                    not (ST.in_range c lo hi la ua (fst (view x (get h x)))) /\
                    not (la && I32.v (S.compare_i32 c lo (fst (view x (get h x)))) > 0) /\
                    S.strictly_sorted c (ST.keys (tree_of view left right h x)))
          (ensures wf left right h (left (get h x)) /\
                   S.strictly_sorted c (ST.keys (tree_of view left right h (left (get h x)))) /\
                   T.size (tree_of view left right h (left (get h x))) < T.size (tree_of view left right h x) /\
                   filter c lo hi la ua (Seq.append (RW.okeys false (tree_of view left right h x)) rest) ==
                   filter c lo hi la ua (Seq.append (RW.okeys false (tree_of view left right h (left (get h x)))) rest))
  = wf_step view left right h x;
    let T.Branch l (k, g) rt = tree_of view left right h x in
    ST.sorted_branch c l k g rt;
    RW.okeys_fwd (tree_of view left right h x);
    RW.okeys_fwd l;
    skip_above c lo hi la ua l k g rt rest

/// A window `ks[n..]` that is `k` followed by `t` starts at `ks[n] == k`, and `t` is `ks[n+1..]`.
let cons_window (#a: Type0) (k: a) (t ks: Seq.seq a) (n: int)
  : Lemma (requires 0 <= n /\ n <= Seq.length ks /\ Seq.cons k t == Seq.slice ks n (Seq.length ks))
          (ensures n < Seq.length ks /\ k == Seq.index ks n /\ t == Seq.slice ks (n + 1) (Seq.length ks))
  = let w = Seq.slice ks n (Seq.length ks) in
    assert (Seq.index (Seq.cons k t) 0 == k);
    assert (Seq.index w 0 == Seq.index ks n);
    let aux (i: nat { i < Seq.length t })
      : Lemma (Seq.index t i == Seq.index (Seq.slice ks (n + 1) (Seq.length ks)) i)
      = assert (Seq.index (Seq.cons k t) (i + 1) == Seq.index t i);
        assert (Seq.index w (i + 1) == Seq.index ks (n + 1 + i))
    in
    FStar.Classical.forall_intro aux;
    Seq.lemma_eq_intro t (Seq.slice ks (n + 1) (Seq.length ks))

/// The pop, for a range-walkable stack whose in-range keys are the window `ks[n..]`: the
/// top's key is `ks[n]`, and its right side and the rest of the stack owe `ks[n+1..]`.
let pop_at (#r #a #b: Type0) (view: B.box r -> r -> (a & b)) (left right: r -> B.box r)
    (h: heap r) (c: O.comparer a) (lo hi: a) (la ua: bool) (s: Seq.seq (B.box r)) (ks: Seq.seq a) (n: int)
  : Lemma (requires Seq.length s > 0 /\ RW.walkable view left right h s /\
                    rwalkable view left right h c lo hi la ua s /\ 0 <= n /\ n <= Seq.length ks /\
                    filter c lo hi la ua (RW.pending view left right false h s) == Seq.slice ks n (Seq.length ks))
          (ensures (let m = Seq.length s - 1 in
                    let x = Seq.index s m in
                    mem h x /\ not (B.is_null x) /\ n < Seq.length ks /\
                    RW.walkable view left right h (Seq.slice s 0 m) /\
                    rwalkable view left right h c lo hi la ua (Seq.slice s 0 m) /\
                    wf left right h (right (get h x)) /\
                    S.strictly_sorted c (ST.keys (tree_of view left right h (right (get h x)))) /\
                    fst (view x (get h x)) == Seq.index ks n /\
                    Seq.length (RW.okeys false (tree_of view left right h (right (get h x)))) +
                      Seq.length (RW.pending view left right false h (Seq.slice s 0 m)) <
                    Seq.length (RW.pending view left right false h s) /\
                    filter c lo hi la ua
                      (Seq.append (RW.okeys false (tree_of view left right h (right (get h x))))
                                  (RW.pending view left right false h (Seq.slice s 0 m))) ==
                    Seq.slice ks (n + 1) (Seq.length ks)))
  = RW.pop view left right false h s;
    let m = Seq.length s - 1 in
    let x = Seq.index s m in
    let s0 = Seq.slice s 0 m in
    assert (forall (i: nat). i < m ==> Seq.index s0 i == Seq.index s i);
    wf_step view left right h x;
    let T.Branch l (k, g) rt = tree_of view left right h x in
    ST.sorted_branch c l k g rt;
    let k = fst (view x (get h x)) in
    let rest = Seq.append (RW.okeys false (tree_of view left right h (right (get h x))))
                          (RW.pending view left right false h s0) in
    filter_cons c lo hi la ua k rest;
    cons_window k (filter c lo hi la ua rest) ks n

(* ---------------------------------------------------------------------------------- *)
(* The breadth-first walk over the region, pruned to the range.                        *)

/// Every pointer in the queue is a node of the region over a strictly sorted subtree.
let rqueue (#r #a #b: Type0) (view: B.box r -> r -> (a & b)) (left right: r -> B.box r)
    (h: heap r) (c: O.comparer a) (q: Seq.seq (B.box r)) : prop =
  forall (i: nat). {:pattern Seq.index q i} i < Seq.length q ==>
    (mem h (Seq.index q i) /\ S.strictly_sorted c (ST.keys (tree_of view left right h (Seq.index q i))))

/// The view's walk queues a child only if the range may reach into it: the left one unless
/// the node is at or under an active lower bound, the right one unless it is at or over an
/// active upper bound.
let rbf_next (#r #a #b: Type0) (view: B.box r -> r -> (a & b)) (left right: r -> B.box r)
    (h: heap r) (c: O.comparer a) (lo hi: a) (la ua: bool)
    (q: Seq.seq (B.box r) { Seq.length q > 0 /\ mem h (Seq.index q 0) }) : GTot (Seq.seq (B.box r)) =
  let x = Seq.index q 0 in
  let rest = Seq.slice q 1 (Seq.length q) in
  let v = get h x in
  let k = fst (view x v) in
  let q1 = if not (B.is_null (left v)) && (not la || I32.v (S.compare_i32 c lo k) < 0) then Seq.snoc rest (left v) else rest in
  if not (B.is_null (right v)) && (not ua || I32.v (S.compare_i32 c hi k) > 0) then Seq.snoc q1 (right v) else q1

/// A visit is about what is owed, not its order: owing a rearrangement is the same visit.
let bf_visited_perm (#a #b: Type0) (keys: Seq.seq a) (tr: Seq.seq ((a & b) & bool)) (p p': Seq.seq a)
  : Lemma (requires RW.bf_visited keys tr p /\ Seq.length p == Seq.length p' /\
                    (forall (y: a). SF.contains p y <==> SF.contains p' y))
          (ensures RW.bf_visited keys tr p')
  = reveal_opaque (`%RW.bf_visited) (RW.bf_visited #a #b)

/// The walk starts with the view's root queued alone, owing every in-range key.
let rbf_start (#r #a #b: Type0) (view: B.box r -> r -> (a & b)) (left right: r -> B.box r)
    (h: heap r) (c: O.comparer a) (lo hi: a) (la ua: bool) (q: Seq.seq (B.box r)) (keys: Seq.seq a)
    (tr: Seq.seq ((a & b) & bool))
  : Lemma (requires Seq.length q == 1 /\ RW.walkable view left right h q /\ Seq.length tr == 0 /\
                    S.strictly_sorted c (ST.keys (tree_of view left right h (Seq.index q 0))) /\
                    filter c lo hi la ua (ST.keys (tree_of view left right h (Seq.index q 0))) == keys)
          (ensures rqueue view left right h c q /\
                   RW.bf_visited keys tr (filter c lo hi la ua (RW.bpending view left right h q)) /\
                   Seq.length (RW.bpending view left right h q) == T.size (tree_of view left right h (Seq.index q 0)))
  = let x = Seq.index q 0 in
    RW.bpending_front view left right h q;
    Seq.lemma_eq_intro (Seq.slice q 1 1) Seq.empty;
    RW.okeys_fwd (tree_of view left right h x);
    Seq.append_empty_r (RW.okeys false (tree_of view left right h x));
    ST.keys_length (tree_of view left right h x);
    RW.bf_start view left right keys tr (filter c lo hi la ua (RW.bpending view left right h q))

/// A sorted node's left side is under its key, its right side over it: when the node is
/// at or under an active lower bound its left side is out of range, and when it is at or
/// over an active upper bound so is its right side.
let prune_left (#a #b: Type0) (c: O.comparer a) (lo hi: a) (la ua: bool)
    (l: T.tree (a & b)) (k: a) (g: b) (r: T.tree (a & b))
  : Lemma (requires S.strictly_sorted c (ST.keys (T.Branch l (k, g) r)) /\ la /\ O.compare c lo k >= 0)
          (ensures filter c lo hi la ua (ST.keys l) == Seq.empty)
  = ST.sorted_branch c l k g r;
    let sl = ST.keys l in
    let out (i: nat) : Lemma (i < Seq.length sl ==> not (ST.in_range c lo hi la ua (Seq.index sl i)))
      = if i < Seq.length sl then O.compare_trans c (Seq.index sl i) k lo else ()
    in
    FStar.Classical.forall_intro out;
    filter_none c lo hi la ua sl

let prune_right (#a #b: Type0) (c: O.comparer a) (lo hi: a) (la ua: bool)
    (l: T.tree (a & b)) (k: a) (g: b) (r: T.tree (a & b))
  : Lemma (requires S.strictly_sorted c (ST.keys (T.Branch l (k, g) r)) /\ ua /\ O.compare c hi k <= 0)
          (ensures filter c lo hi la ua (ST.keys r) == Seq.empty)
  = ST.sorted_branch c l k g r;
    let sr = ST.keys r in
    let out (i: nat) : Lemma (i < Seq.length sr ==> not (ST.in_range c lo hi la ua (Seq.index sr i)))
      = if i < Seq.length sr then O.compare_trans c hi k (Seq.index sr i) else ()
    in
    FStar.Classical.forall_intro out;
    filter_none c lo hi la ua sr

/// `compare_i32`'s sign is the comparer's.
let compare_i32_sign (#a: Type0) (c: O.comparer a) (x y: a)
  : Lemma ((I32.v (S.compare_i32 c x y) < 0 <==> O.compare c x y < 0) /\
           (I32.v (S.compare_i32 c x y) > 0 <==> O.compare c x y > 0))
  = ()

/// What the walk leaves unqueued owes nothing in range: a null child owes nothing at all,
/// and a pruned one (R35.14) is on the far side of a bound.
let rbf_prune (#r #a #b: Type0) (view: B.box r -> r -> (a & b)) (left right: r -> B.box r)
    (h: heap r) (c: O.comparer a) (lo hi: a) (la ua: bool) (x: B.box r)
  : Lemma (requires wf left right h x /\ not (B.is_null x) /\
                    S.strictly_sorted c (ST.keys (tree_of view left right h x)))
          (ensures (let v = get h x in
                    let k = fst (view x v) in
                    (not (not (B.is_null (left v)) && (not la || I32.v (S.compare_i32 c lo k) < 0)) ==>
                       filter c lo hi la ua (ST.keys (tree_of view left right h (left v))) == Seq.empty) /\
                    (not (not (B.is_null (right v)) && (not ua || I32.v (S.compare_i32 c hi k) > 0)) ==>
                       filter c lo hi la ua (ST.keys (tree_of view left right h (right v))) == Seq.empty)))
  = wf_step view left right h x;
    let v = get h x in
    let T.Branch tl (k, g) trr = tree_of view left right h x in
    compare_i32_sign c lo k;
    compare_i32_sign c hi k;
    if B.is_null (left v) then ()
    else if la && O.compare c lo k >= 0 then prune_left c lo hi la ua tl k g trr
    else ();
    if B.is_null (right v) then ()
    else if ua && O.compare c hi k <= 0 then prune_right c lo hi la ua tl k g trr
    else ()

/// What `rbf_next` owes, in terms of what the front's children and the rest of the queue do.
let rbf_next_pending (#r #a #b: Type0) (view: B.box r -> r -> (a & b)) (left right: r -> B.box r)
    (h: heap r) (c: O.comparer a) (lo hi: a) (la ua: bool) (q: Seq.seq (B.box r))
  : Lemma (requires Seq.length q > 0 /\ RW.walkable view left right h q /\ rqueue view left right h c q)
          (ensures (let x = Seq.index q 0 in
                    let v = get h x in
                    let rest = Seq.slice q 1 (Seq.length q) in
                    let q' = rbf_next view left right h c lo hi la ua q in
                    let l = ST.keys (tree_of view left right h (left v)) in
                    let rt = ST.keys (tree_of view left right h (right v)) in
                    RW.walkable view left right h q' /\ rqueue view left right h c q' /\
                    wf left right h (left v) /\ wf left right h (right v) /\
                    filter c lo hi la ua (RW.bpending view left right h q') ==
                      Seq.append (Seq.append (filter c lo hi la ua (RW.bpending view left right h rest))
                                             (filter c lo hi la ua l))
                                 (filter c lo hi la ua rt) /\
                    Seq.length (RW.bpending view left right h q') <= 
                      Seq.length (RW.bpending view left right h rest) + Seq.length l + Seq.length rt))
  = let x = Seq.index q 0 in
    let rest = Seq.slice q 1 (Seq.length q) in
    wf_step view left right h x;
    let v = get h x in
    let k = fst (view x v) in
    let T.Branch tl (k0, g) trr = tree_of view left right h x in
    ST.sorted_branch c tl k0 g trr;
    rbf_prune view left right h c lo hi la ua x;
    let l = ST.keys tl in
    let rt = ST.keys trr in
    let br = RW.bpending view left right h rest in
    let fl = filter c lo hi la ua l in
    let fr = filter c lo hi la ua rt in
    let fb = filter c lo hi la ua br in
    let el = not (B.is_null (left v)) && (not la || I32.v (S.compare_i32 c lo k) < 0) in
    let er = not (B.is_null (right v)) && (not ua || I32.v (S.compare_i32 c hi k) > 0) in
    if el then wf_step view left right h (left v);
    if er then wf_step view left right h (right v);
    let q1 = if el then Seq.snoc rest (left v) else rest in
    let q' = rbf_next view left right h c lo hi la ua q in
    let p1 = if el then Seq.append br l else br in
    (if el then RW.bpending_snoc view left right h rest (left v));
    assert (RW.bpending view left right h q1 == p1);
    let p' = if er then Seq.append p1 rt else p1 in
    (if er then RW.bpending_snoc view left right h q1 (right v));
    assert (RW.bpending view left right h q' == p');
    (if el then filter_append c lo hi la ua br l else Seq.append_empty_r fb);
    let fp1 = filter c lo hi la ua p1 in
    assert (fp1 == Seq.append fb fl);
    (if er then filter_append c lo hi la ua p1 rt else Seq.append_empty_r fp1);
    assert (filter c lo hi la ua p' == Seq.append fp1 fr);
    let idx1 (i: nat) : Lemma (i < Seq.length q1 ==>
                               Seq.index q1 i == (if i < Seq.length rest then Seq.index q (i + 1) else left v))
      = () in
    FStar.Classical.forall_intro idx1;
    let idx' (i: nat) : Lemma (i < Seq.length q' ==>
                               Seq.index q' i == (if i < Seq.length q1 then Seq.index q1 i else right v))
      = () in
    FStar.Classical.forall_intro idx'

/// R35.14. One round of the view's breadth-first walk: take the front `x` off the queue,
/// call the callback on it if it is in range, and queue the children the range may reach
/// (`rbf_next`). The queue owes strictly less afterwards; an in-range call that returns
/// true, or no call, keeps the visit at the next queue; an in-range call that returns
/// false ends it.
let rbf_dequeue (#r #a #b: Type0) (view: B.box r -> r -> (a & b)) (left right: r -> B.box r)
    (h: heap r) (c: O.comparer a) (lo hi: a) (la ua: bool)
    (q: Seq.seq (B.box r)) (keys: Seq.seq a) (tr: Seq.seq ((a & b) & bool))
  : Lemma (requires Seq.length q > 0 /\ RW.walkable view left right h q /\ rqueue view left right h c q /\
                    RW.bf_visited keys tr (filter c lo hi la ua (RW.bpending view left right h q)))
          (ensures (let x = Seq.index q 0 in
                    mem h x /\ not (B.is_null x) /\
                    (let v = get h x in
                     let q' = rbf_next view left right h c lo hi la ua q in
                     wf left right h (left v) /\ wf left right h (right v) /\
                     RW.walkable view left right h q' /\ rqueue view left right h c q' /\
                     Seq.length q' <= Seq.length (RW.bpending view left right h q') /\
                     Seq.length (RW.bpending view left right h q') < Seq.length (RW.bpending view left right h q) /\
                     (ST.in_range c lo hi la ua (fst (view x v)) ==>
                        Seq.length tr < Seq.length keys /\
                        RW.bf_visited keys (Seq.snoc tr (view x v, true))
                          (filter c lo hi la ua (RW.bpending view left right h q')) /\
                        RW.bf_walked keys (Seq.snoc tr (view x v, false)) false) /\
                     (not (ST.in_range c lo hi la ua (fst (view x v))) ==>
                        RW.bf_visited keys tr (filter c lo hi la ua (RW.bpending view left right h q'))))))
  = let x = Seq.index q 0 in
    let rest = Seq.slice q 1 (Seq.length q) in
    RW.bf_front view left right h q;
    rbf_next_pending view left right h c lo hi la ua q;
    let v = get h x in
    let k = fst (view x v) in
    let q' = rbf_next view left right h c lo hi la ua q in
    RW.bwalkable_length view left right h q';
    let tl = tree_of view left right h (left v) in
    let trr = tree_of view left right h (right v) in
    let l = ST.keys tl in
    let rt = ST.keys trr in
    let br = RW.bpending view left right h rest in
    let fl = filter c lo hi la ua l in
    let fr = filter c lo hi la ua rt in
    let fb = filter c lo hi la ua br in
    let fq' = filter c lo hi la ua (RW.bpending view left right h q') in
    assert (fq' == Seq.append (Seq.append fb fl) fr);
    filter_append c lo hi la ua (Seq.append l (Seq.cons k rt)) br;
    filter_append c lo hi la ua l (Seq.cons k rt);
    filter_cons c lo hi la ua k rt;
    let fq = filter c lo hi la ua (RW.bpending view left right h q) in
    if ST.in_range c lo hi la ua k then begin
      assert (fq == Seq.append (Seq.append fl (Seq.cons k fr)) fb);
      RW.bf_step keys tr fl k fr fb (view x v, true);
      RW.bf_step keys tr fl k fr fb (view x v, false)
    end else begin
      assert (fq == Seq.append (Seq.append fl fr) fb);
      let aux (y: a) : Lemma (SF.contains fq y <==> SF.contains fq' y)
        = SF.contains_append (Seq.append fl fr) fb y;
          SF.contains_append fl fr y;
          SF.contains_append (Seq.append fb fl) fr y;
          SF.contains_append fb fl y in
      FStar.Classical.forall_intro aux;
      bf_visited_perm keys tr fq fq'
    end

(* ---------------------------------------------------------------------------------- *)
(* R35.17. The view's `MinInternal`/`MaxInternal`: a descent from the view's root to the  *)
(* least (greatest) in-range key. Only the lower (upper) bound is tested on the way: every *)
(* key the descent can stop at is below (above) the root, which is within the other bound. *)

let first_or (#a: Type0) (s: Seq.seq a) (d: a) : a =
  if Seq.length s > 0 then Seq.index s 0 else d

let last_or (#a: Type0) (s: Seq.seq a) (d: a) : a =
  if Seq.length s > 0 then Seq.index s (Seq.length s - 1) else d

let first_or_append (#a: Type0) (s t: Seq.seq a) (d: a)
  : Lemma (first_or (Seq.append s t) d == first_or s (first_or t d))
  = ()

let last_or_append (#a: Type0) (s t: Seq.seq a) (d: a)
  : Lemma (last_or (Seq.append s t) d == last_or t (last_or s d))
  = ()

/// Within the upper bound, the upper bound filters nothing out.
let rec filter_upper_free (#a: Type0) (c: O.comparer a) (lo hi: a) (la ua: bool) (s: Seq.seq a)
  : Lemma (requires forall (i: nat). i < Seq.length s ==> ua ==> O.compare c (Seq.index s i) hi <= 0)
          (ensures filter c lo hi la ua s == filter c lo hi la false s)
          (decreases Seq.length s)
  = if Seq.length s = 0 then ()
    else begin
      assert (forall (i: nat). i < Seq.length (Seq.tail s) ==> Seq.index (Seq.tail s) i == Seq.index s (i + 1));
      filter_upper_free c lo hi la ua (Seq.tail s)
    end

/// Within the lower bound, the lower bound filters nothing out.
let rec filter_lower_free (#a: Type0) (c: O.comparer a) (lo hi: a) (la ua: bool) (s: Seq.seq a)
  : Lemma (requires forall (i: nat). i < Seq.length s ==> la ==> O.compare c lo (Seq.index s i) <= 0)
          (ensures filter c lo hi la ua s == filter c lo hi false ua s)
          (decreases Seq.length s)
  = if Seq.length s = 0 then ()
    else begin
      assert (forall (i: nat). i < Seq.length (Seq.tail s) ==> Seq.index (Seq.tail s) i == Seq.index s (i + 1));
      filter_lower_free c lo hi la ua (Seq.tail s)
    end

/// The range search stops at an in-range key, if at any.
let rec range_root_key (#a #b: Type0) (c: O.comparer a) (t: T.tree (a & b)) (lo hi: a) (la ua: bool)
  : Lemma (ensures (match ST.range_root c t lo hi la ua with
                    | T.Branch _ (k, _) _ -> ST.in_range c lo hi la ua k
                    | T.Leaf -> True))
          (decreases t)
  = match t with
    | T.Leaf -> ()
    | T.Branch l (v, _) r ->
      if la && O.compare c lo v > 0 then range_root_key c r lo hi la ua
      else if ua && O.compare c hi v < 0 then range_root_key c l lo hi la ua
      else ()

/// The descent's step at a branch of a sorted tree, testing the lower bound as the code does
/// (`comp > 0` moves right; else the key is a candidate, and `comp == 0` is the answer).
let min_step (#a #b: Type0) (c: O.comparer a) (lo hi: a) (la: bool) (t: T.tree (a & b)) (d: a)
  : Lemma (requires T.Branch? t /\ S.strictly_sorted c (ST.keys t))
          (ensures (match t with
                    | T.Branch l (k, _) r ->
                      S.strictly_sorted c (ST.keys l) /\ S.strictly_sorted c (ST.keys r) /\
                      T.size l < T.size t /\ T.size r < T.size t /\
                      (la /\ I32.v (S.compare_i32 c lo k) > 0 ==>
                         first_or (filter c lo hi la false (ST.keys t)) d ==
                         first_or (filter c lo hi la false (ST.keys r)) d) /\
                      (~(la /\ I32.v (S.compare_i32 c lo k) > 0) ==>
                         first_or (filter c lo hi la false (ST.keys t)) d ==
                         first_or (filter c lo hi la false (ST.keys l)) k) /\
                      (la /\ I32.v (S.compare_i32 c lo k) == 0 ==>
                         first_or (filter c lo hi la false (ST.keys l)) k == k)
                    | _ -> True))
  = let T.Branch l (k, g) r = t in
    ST.sorted_branch c l k g r;
    let sl = ST.keys l in
    let sr = ST.keys r in
    if la && O.compare c lo k > 0 then begin
      skip_below c lo hi la false l k g r Seq.empty;
      Seq.append_empty_r (ST.keys t);
      Seq.append_empty_r sr
    end
    else begin
      filter_append c lo hi la false sl (Seq.cons k sr);
      filter_cons c lo hi la false k sr;
      first_or_append (filter c lo hi la false sl) (Seq.cons k (filter c lo hi la false sr)) d;
      if la && O.compare c lo k = 0 then begin
        let out (i: nat) : Lemma (i < Seq.length sl ==> not (ST.in_range c lo hi la false (Seq.index sl i)))
          = if i < Seq.length sl then O.compare_trans c (Seq.index sl i) k lo else ()
        in
        FStar.Classical.forall_intro out;
        filter_none c lo hi la false sl
      end
    end

/// The descent's step for the greatest key (`comp < 0` moves left).
let max_step (#a #b: Type0) (c: O.comparer a) (lo hi: a) (ua: bool) (t: T.tree (a & b)) (d: a)
  : Lemma (requires T.Branch? t /\ S.strictly_sorted c (ST.keys t))
          (ensures (match t with
                    | T.Branch l (k, _) r ->
                      S.strictly_sorted c (ST.keys l) /\ S.strictly_sorted c (ST.keys r) /\
                      T.size l < T.size t /\ T.size r < T.size t /\
                      (ua /\ I32.v (S.compare_i32 c hi k) < 0 ==>
                         last_or (filter c lo hi false ua (ST.keys t)) d ==
                         last_or (filter c lo hi false ua (ST.keys l)) d) /\
                      (~(ua /\ I32.v (S.compare_i32 c hi k) < 0) ==>
                         last_or (filter c lo hi false ua (ST.keys t)) d ==
                         last_or (filter c lo hi false ua (ST.keys r)) k) /\
                      (ua /\ I32.v (S.compare_i32 c hi k) == 0 ==>
                         last_or (filter c lo hi false ua (ST.keys r)) k == k)
                    | _ -> True))
  = let T.Branch l (k, g) r = t in
    ST.sorted_branch c l k g r;
    let sl = ST.keys l in
    let sr = ST.keys r in
    if ua && O.compare c hi k < 0 then begin
      skip_above c lo hi false ua l k g r Seq.empty;
      Seq.append_empty_r (ST.keys t);
      Seq.append_empty_r sl
    end
    else begin
      filter_append c lo hi false ua sl (Seq.cons k sr);
      filter_cons c lo hi false ua k sr;
      last_or_append (filter c lo hi false ua sl) (Seq.cons k (filter c lo hi false ua sr)) d;
      if ua && O.compare c hi k = 0 then begin
        let out (i: nat) : Lemma (i < Seq.length sr ==> not (ST.in_range c lo hi false ua (Seq.index sr i)))
          = if i < Seq.length sr then O.compare_trans c hi k (Seq.index sr i) else ()
        in
        FStar.Classical.forall_intro out;
        filter_none c lo hi false ua sr
      end
    end

/// The descent starts at the view's root: its least key within the lower bound is the
/// least in-range key of the whole tree, and its greatest key within the upper bound the
/// greatest.
let min_max_goal (#a #b: Type0) (c: O.comparer a) (t: T.tree (a & b)) (lo hi: a) (la ua: bool) (d: a)
  : Lemma (requires S.strictly_sorted c (ST.keys t))
          (ensures S.strictly_sorted c (ST.keys (ST.range_root c t lo hi la ua)) /\
                   first_or (filter c lo hi la false (ST.keys (ST.range_root c t lo hi la ua))) d ==
                   first_or (filter c lo hi la ua (ST.keys t)) d /\
                   last_or (filter c lo hi false ua (ST.keys (ST.range_root c t lo hi la ua))) d ==
                   last_or (filter c lo hi la ua (ST.keys t)) d)
  = range_root_filter c t lo hi la ua;
    range_root_key c t lo hi la ua;
    match ST.range_root c t lo hi la ua with
    | T.Leaf -> ()
    | T.Branch l (k, g) r ->
      ST.sorted_branch c l k g r;
      let sl = ST.keys l in
      let sr = ST.keys r in
      let ul (i: nat) : Lemma (i < Seq.length sl ==> ua ==> O.compare c (Seq.index sl i) hi <= 0)
        = if i < Seq.length sl && ua then O.compare_trans c (Seq.index sl i) k hi else ()
      in
      let lr (i: nat) : Lemma (i < Seq.length sr ==> la ==> O.compare c lo (Seq.index sr i) <= 0)
        = if i < Seq.length sr && la then O.compare_trans c lo k (Seq.index sr i) else ()
      in
      FStar.Classical.forall_intro ul;
      FStar.Classical.forall_intro lr;
      filter_upper_free c lo hi la ua sl;
      filter_lower_free c lo hi la ua sr;
      filter_append c lo hi la ua sl (Seq.cons k sr);
      filter_append c lo hi la false sl (Seq.cons k sr);
      filter_append c lo hi false ua sl (Seq.cons k sr);
      filter_cons c lo hi la ua k sr;
      filter_cons c lo hi la false k sr;
      filter_cons c lo hi false ua k sr;
      first_or_append (filter c lo hi la ua sl) (Seq.cons k (filter c lo hi la ua sr)) d;
      first_or_append (filter c lo hi la false sl) (Seq.cons k (filter c lo hi la false sr)) d;
      last_or_append (filter c lo hi la ua sl) (Seq.cons k (filter c lo hi la ua sr)) d;
      last_or_append (filter c lo hi false ua sl) (Seq.cons k (filter c lo hi false ua sr)) d

let all_true (#e: Type0) (tr: Seq.seq (e & bool)) : prop =
  forall (i: nat). i < Seq.length tr ==> snd (Seq.index tr i) == true

let all_true_snoc (#e: Type0) (tr: Seq.seq (e & bool)) (x: e & bool)
  : Lemma (requires all_true tr /\ snd x == true)
          (ensures all_true (Seq.snoc tr x))
          [SMTPat (all_true (Seq.snoc tr x))]
  = ()

let all_true_empty (e: Type0)
  : Lemma (all_true #e Seq.empty)
          [SMTPat (all_true #e Seq.empty)]
  = ()

let counted (#a #b: Type0) (keys: Seq.seq a) (tr: Seq.seq ((a & b) & bool)) (res: bool)
  : Lemma (requires RW.walked keys tr res /\ all_true tr)
          (ensures Seq.length tr == Seq.length keys)
          [SMTPat (RW.walked keys tr res); SMTPat (all_true tr)]
  = ()
