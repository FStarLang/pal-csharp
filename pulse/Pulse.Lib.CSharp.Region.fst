module Pulse.Lib.CSharp.Region
#lang-pulse

/// A *region* of boxes (doc/translation.md §27): every object of one `[Region]` class that a
/// structure owns, held as one resource over a ghost heap. Reads, writes and allocations go
/// through the heap, so the nodes can alias, be re-linked and be reached by any path, and the
/// shape of what the heap describes is a pure function of it (`tree_n`).
///
/// Trusted: only `Pulse.Lib.CSharp.RefEq.ref_eq` (R27.8).

open Pulse.Lib.Pervasives
module B = Pulse.Lib.Box
module R = Pulse.Lib.Reference
module L = FStar.List.Tot
module T = Pulse.Lib.CSharp.Tree
module Tac = FStar.Tactics.V2

/// The heap: each owned box with the record it holds.
let heap (a: Type0) = list (B.box a & a)

/// Box equality is decided by R27.8's `ref_eq`, the one trusted fact this module uses.
let eq_box (#a: Type0) (x y: B.box a) : bool = Pulse.Lib.CSharp.RefEq.ref_eq x y

let rec lookup (#a: Type0) (h: heap a) (x: B.box a) : Tot (option a) (decreases h) =
  match h with
  | [] -> None
  | (b, v) :: t -> if eq_box b x then Some v else lookup t x

let mem (#a: Type0) (h: heap a) (x: B.box a) : prop = Some? (lookup h x)

let get (#a: Type0) (h: heap a) (x: B.box a { mem h x }) : a = Some?.v (lookup h x)

let rec upd (#a: Type0) (h: heap a) (x: B.box a) (v: a) : Tot (heap a) (decreases h) =
  match h with
  | [] -> []
  | (b, w) :: t -> if eq_box b x then (b, v) :: t else (b, w) :: upd t x v

let rec remove (#a: Type0) (h: heap a) (x: B.box a) : Tot (heap a) (decreases h) =
  match h with
  | [] -> []
  | (b, w) :: t -> if eq_box b x then t else (b, w) :: remove t x

let rec lookup_upd (#a: Type0) (h: heap a) (x y: B.box a) (v: a)
  : Lemma (ensures lookup (upd h x v) y ==
                   (if eq_box x y && Some? (lookup h x) then Some v else lookup h y))
          (decreases h)
          [SMTPat (lookup (upd h x v) y)]
  = match h with
    | [] -> ()
    | (b, w) :: t -> lookup_upd t x y v

let rec length_upd (#a: Type0) (h: heap a) (x: B.box a) (v: a)
  : Lemma (ensures L.length (upd h x v) == L.length h) (decreases h)
          [SMTPat (L.length (upd h x v))]
  = match h with
    | [] -> ()
    | _ :: t -> length_upd t x v

let rec upd_same (#a: Type0) (h: heap a) (x: B.box a)
  : Lemma (requires mem h x) (ensures upd h x (get h x) == h) (decreases h)
  = match h with
    | (b, w) :: t -> if eq_box b x then () else upd_same t x

/// The cells of a heap, each at permission `p`.
let rec cells (#a: Type0) (p: perm) (h: heap a) : Tot slprop (decreases h) =
  match h with
  | [] -> emp
  | (b, v) :: t -> B.pts_to b #p v ** cells p t

/// R27.4. The resource a region-owning class's invariant holds.
let region (#a: Type0) (#[Tac.exact (`1.0R)] p: perm) (h: heap a) : slprop =
  cells p h

ghost fn rec take (#a: Type0) (#p: perm) (h: heap a) (x: B.box a)
  requires cells p h ** pure (mem h x)
  returns  v: erased a
  ensures  B.pts_to x #p v ** cells p (remove h x) ** pure (lookup h x == Some (reveal v))
  decreases h
{
  match h {
    Nil -> { unreachable () }
    Cons hd t -> {
      let b = fst hd;
      let w = snd hd;
      rewrite (cells p h) as (B.pts_to b #p w ** cells p t);
      if (eq_box b x) {
        rewrite (B.pts_to b #p w) as (B.pts_to x #p w);
        rewrite (cells p t) as (cells p (remove h x));
        hide w
      } else {
        let v = take t x;
        fold (cells p ((b, w) :: remove t x));
        rewrite (cells p ((b, w) :: remove t x)) as (cells p (remove h x));
        v
      }
    }
  }
}

ghost fn rec put (#a: Type0) (#p: perm) (h: heap a) (x: B.box a) (v: a)
  requires B.pts_to x #p v ** cells p (remove h x) ** pure (mem h x)
  ensures  cells p (upd h x v)
  decreases h
{
  match h {
    Nil -> { unreachable () }
    Cons hd t -> {
      let b = fst hd;
      let w = snd hd;
      if (eq_box b x) {
        rewrite (cells p (remove h x)) as (cells p t);
        rewrite (B.pts_to x #p v) as (B.pts_to b #p v);
        fold (cells p ((b, v) :: t));
        rewrite (cells p ((b, v) :: t)) as (cells p (upd h x v));
      } else {
        rewrite (cells p (remove h x)) as (B.pts_to b #p w ** cells p (remove t x));
        put t x v;
        fold (cells p ((b, w) :: upd t x v));
        rewrite (cells p ((b, w) :: upd t x v)) as (cells p (upd h x v));
      }
    }
  }
}

/// R27.6. An owner's region starts empty.
ghost fn empty (#a: Type0) ()
  ensures region #a ([] <: heap a)
{
  fold (cells #a 1.0R []);
  fold (region #a #1.0R ([] <: heap a))
}

/// R27.25. The heap the region holds now. It does nothing; its `rewrites_to` is what
/// lets a loop's `decreases` name a heap the invariant quantifies, as `!r` names a cell.
ghost fn current (#a: Type0) (#p: perm) (#h: erased (heap a)) (_: unit)
  preserves region #a #p h
  returns  r: heap a
  ensures  rewrites_to r (reveal h)
{
  reveal h
}

/// R27.5. Reading an object of the region: `x.f` is `(read x).f`.
fn read (#a: Type0) (x: B.box a) (#p: perm) (#h: erased (heap a))
  preserves region #a #p h
  requires pure (mem h x)
  returns  v: a
  ensures  pure (mem h x /\ not (B.is_null x) /\ v == get h x)
{
  unfold (region #a #p h);
  let _ = take h x;
  B.pts_to_not_null x;
  let v = B.(!x);
  put h x v;
  upd_same h x;
  rewrite (cells p (upd h x v)) as (cells p h);
  fold (region #a #p h);
  v
}

/// R31.11. Reading the owner a node points back to (`list!.head` in a ring node's member):
/// the member is given the owner's box `o`, at some permission, and a pointer `x` read
/// from the node that the precondition says is `o`. The read goes through `x`.
fn read_owner (#b: Type0) (o: erased (B.box b)) (x: B.box b) (#p: perm) (#r: erased b)
  preserves B.pts_to (reveal o) #p r
  requires pure (x == reveal o)
  returns  v: b
  ensures  pure (v == reveal r)
{
  rewrite (B.pts_to (reveal o) #p r) as (B.pts_to x #p r);
  let v = B.(!x);
  rewrite (B.pts_to x #p r) as (B.pts_to (reveal o) #p r);
  v
}

/// R27.5. Writing a field: the whole record is replaced in place.
fn write (#a: Type0) (x: B.box a) (v: a) (#h: erased (heap a))
  requires region h ** pure (mem h x)
  ensures  region (upd h x v)
{
  unfold (region #a #1.0R h);
  let _ = take h x;
  B.(x := v);
  put h x v;
  fold (region #a #1.0R (upd h x v));
}

ghost fn rec fresh (#a: Type0) (h: heap a) (x: B.box a) (#v: a)
  preserves cells 1.0R h ** B.pts_to x #1.0R v
  ensures  pure (~ (mem h x))
  decreases h
{
  match h {
    Nil -> { () }
    Cons hd t -> {
      let b = fst hd;
      let w = snd hd;
      rewrite (cells 1.0R h) as (B.pts_to b #1.0R w ** cells 1.0R t);
      fresh t x;
      if (eq_box b x) {
        rewrite (B.pts_to b #1.0R w) as (B.pts_to x #1.0R w);
        B.gather x;
        B.to_ref_pts_to x;
        R.pts_to_perm_bound (B.box_to_ref x);
        unreachable ()
      } else {
        fold (cells 1.0R ((b, w) :: t));
        rewrite (cells 1.0R ((b, w) :: t)) as (cells 1.0R h);
      }
    }
  }
}

/// R27.6. `new N(...)` on a region class: a fresh box, added to the heap.
fn alloc (#a: Type0) (v: a) (#h: erased (heap a))
  requires region h
  returns  x: B.box a
  ensures  region ((x, v) :: h) ** pure (not (B.is_null x) /\ ~ (mem h x))
{
  unfold (region #a #1.0R h);
  let x = B.alloc v;
  B.pts_to_not_null x;
  fresh h x;
  fold (cells 1.0R ((x, v) :: h));
  fold (region #a #1.0R ((x, v) :: h));
  x
}

ghost fn rec cells_share (#a: Type0) (#p: perm) (h: heap a)
  requires cells p h
  ensures  cells (p /. 2.0R) h ** cells (p /. 2.0R) h
  decreases h
{
  match h {
    Nil -> {
      rewrite (cells p h) as emp;
      fold (cells (p /. 2.0R) ([] <: heap a));
      fold (cells (p /. 2.0R) ([] <: heap a));
      rewrite (cells (p /. 2.0R) ([] <: heap a)) as (cells (p /. 2.0R) h);
      rewrite (cells (p /. 2.0R) ([] <: heap a)) as (cells (p /. 2.0R) h);
    }
    Cons hd t -> {
      let b = fst hd;
      let w = snd hd;
      rewrite (cells p h) as (B.pts_to b #p w ** cells p t);
      B.share b;
      cells_share t;
      fold (cells (p /. 2.0R) ((b, w) :: t));
      fold (cells (p /. 2.0R) ((b, w) :: t));
      rewrite (cells (p /. 2.0R) ((b, w) :: t)) as (cells (p /. 2.0R) h);
      rewrite (cells (p /. 2.0R) ((b, w) :: t)) as (cells (p /. 2.0R) h);
    }
  }
}

ghost fn region_share (#a: Type0) (#p: perm) (h: heap a)
  requires region #a #p h
  ensures  region #a #(p /. 2.0R) h ** region #a #(p /. 2.0R) h
{
  unfold (region #a #p h);
  cells_share h;
  fold (region #a #(p /. 2.0R) h);
  fold (region #a #(p /. 2.0R) h);
}

ghost fn rec cells_gather (#a: Type0) (#p #q: perm) (h: heap a)
  requires cells p h ** cells q h
  ensures  cells (p +. q) h
  decreases h
{
  match h {
    Nil -> {
      rewrite (cells p h) as emp;
      rewrite (cells q h) as emp;
      fold (cells (p +. q) ([] <: heap a));
      rewrite (cells (p +. q) ([] <: heap a)) as (cells (p +. q) h);
    }
    Cons hd t -> {
      let b = fst hd;
      let w = snd hd;
      rewrite (cells p h) as (B.pts_to b #p w ** cells p t);
      rewrite (cells q h) as (B.pts_to b #q w ** cells q t);
      B.gather b;
      cells_gather #a #p #q t;
      fold (cells (p +. q) ((b, w) :: t));
      rewrite (cells (p +. q) ((b, w) :: t)) as (cells (p +. q) h);
    }
  }
}

/// Two halves of one region over the same heap are the whole of it. (Two halves of one
/// object's invariant name the same heap because the heap is determined by the record
/// they share -- see `wf`.)
ghost fn region_gather (#a: Type0) (#p #q: perm) (h: heap a)
  requires region #a #p h ** region #a #q h
  ensures  region #a #(p +. q) h
{
  unfold (region #a #p h);
  unfold (region #a #q h);
  cells_gather #a #p #q h;
  fold (region #a #(p +. q) h);
}

(* ---------------------------------------------------------------------------------- *)
(* The shape a heap describes.                                                          *)

/// R27.7. The tree reachable from `x` through `left` and `right`, each node seen through
/// `view`, unfolded at most `n` deep.
let rec tree_n (#a #v: Type0) (view: B.box a -> a -> v) (left right: a -> B.box a)
    (n: nat) (h: heap a) (x: B.box a)
  : GTot (T.tree v) (decreases n)
  = if n = 0 || B.is_null x then T.Leaf
    else match lookup h x with
      | None -> T.Leaf
      | Some r -> T.Branch (tree_n view left right (n - 1) h (left r))
                           (view x r)
                           (tree_n view left right (n - 1) h (right r))

/// `x` reaches only boxes of `h` within `n` steps, and null ends every path.
let rec closed (#a: Type0) (left right: a -> B.box a) (n: nat) (h: heap a) (x: B.box a)
  : GTot prop (decreases n)
  = B.is_null x \/
    (n > 0 /\ mem h x /\
     closed left right (n - 1) h (left (get h x)) /\
     closed left right (n - 1) h (right (get h x)))

let fuel (#a: Type0) (h: heap a) : nat = L.length h + 1

/// R27.7. The whole tree at `x`. Opaque to the solver, as `wf` is (R27.16): what a proof
/// knows of either comes from the lemmas below, a step at a time, and not from unrolling a
/// recursion whose fuel is the size of the heap.
[@@"opaque_to_smt"]
let tree_of (#a #v: Type0) (view: B.box a -> a -> v) (left right: a -> B.box a)
    (h: heap a) (x: B.box a) : GTot (T.tree v)
  = tree_n view left right (fuel h) h x

/// R27.4. What an owner's invariant says of the region beside the pointer it holds.
[@@"opaque_to_smt"]
let wf (#a: Type0) (left right: a -> B.box a) (h: heap a) (x: B.box a) : prop =
  closed left right (fuel h) h x

let rec closed_mono (#a: Type0) (left right: a -> B.box a) (m n: nat) (h: heap a) (x: B.box a)
  : Lemma (requires closed left right m h x /\ m <= n)
          (ensures closed left right n h x) (decreases m)
  = if B.is_null x then ()
    else (closed_mono left right (m - 1) (n - 1) h (left (get h x));
          closed_mono left right (m - 1) (n - 1) h (right (get h x)))

let rec tree_n_mono (#a #v: Type0) (view: B.box a -> a -> v) (left right: a -> B.box a)
    (m n: nat) (h: heap a) (x: B.box a)
  : Lemma (requires closed left right m h x /\ m <= n)
          (ensures tree_n view left right m h x == tree_n view left right n h x) (decreases m)
  = if B.is_null x then ()
    else (tree_n_mono view left right (m - 1) (n - 1) h (left (get h x));
          tree_n_mono view left right (m - 1) (n - 1) h (right (get h x)))

/// A well-formed non-null root is a branch over its children's trees, and they are
/// well-formed: what a descent needs to take one step.
let wf_step (#a #v: Type0) (view: B.box a -> a -> v) (left right: a -> B.box a)
    (h: heap a) (x: B.box a)
  : Lemma (requires wf left right h x /\ not (B.is_null x))
          (ensures mem h x /\
                   wf left right h (left (get h x)) /\ wf left right h (right (get h x)) /\
                   tree_of view left right h x ==
                     T.Branch (tree_of view left right h (left (get h x)))
                              (view x (get h x))
                              (tree_of view left right h (right (get h x))))
  = reveal_opaque (`%wf) (wf #a); reveal_opaque (`%tree_of) (tree_of #a #v);
    let r = get h x in
    closed_mono left right (fuel h - 1) (fuel h) h (left r);
    closed_mono left right (fuel h - 1) (fuel h) h (right r);
    tree_n_mono view left right (fuel h - 1) (fuel h) h (left r);
    tree_n_mono view left right (fuel h - 1) (fuel h) h (right r)

let wf_null (#a #v: Type0) (view: B.box a -> a -> v) (left right: a -> B.box a)
    (h: heap a) (x: B.box a)
  : Lemma (requires B.is_null x)
          (ensures wf left right h x /\ tree_of view left right h x == T.Leaf)
          [SMTPat (tree_of view left right h x)]
  = reveal_opaque (`%wf) (wf #a); reveal_opaque (`%tree_of) (tree_of #a #v)

/// The root of the tree at a box of the heap, well-formed or not.
let tree_of_mem (#a #v: Type0) (view: B.box a -> a -> v) (left right: a -> B.box a)
    (h: heap a) (x: B.box a)
  : Lemma (requires mem h x /\ not (B.is_null x))
          (ensures tree_of view left right h x ==
                   T.Branch (tree_n view left right (L.length h) h (left (get h x)))
                            (view x (get h x))
                            (tree_n view left right (L.length h) h (right (get h x))))
          [SMTPat (tree_of view left right h x)]
  = reveal_opaque (`%tree_of) (tree_of #a #v)

let wf_null_wf (#a: Type0) (left right: a -> B.box a) (h: heap a) (x: B.box a)
  : Lemma (requires B.is_null x) (ensures wf left right h x) [SMTPat (wf left right h x)]
  = reveal_opaque (`%wf) (wf #a)

/// R27.5. `wf_step` in the form a read states it: conditional, so a reader of a pointer
/// that is not known to be well-formed is not refused.
let wf_step_if (#a #v: Type0) (view: B.box a -> a -> v) (left right: a -> B.box a)
    (h: heap a) (x: B.box a)
  : Lemma (requires mem h x /\ not (B.is_null x))
          (ensures wf left right h x ==>
                   (wf left right h (left (get h x)) /\ wf left right h (right (get h x)) /\
                    tree_of view left right h x ==
                      T.Branch (tree_of view left right h (left (get h x)))
                               (view x (get h x))
                               (tree_of view left right h (right (get h x)))))
  = FStar.Classical.move_requires (wf_step view left right h) x

/// R27.5. What a read needs: the box is in the heap, which a well-formed non-null pointer is.
let mem_of_wf (#a: Type0) (left right: a -> B.box a) (h: heap a) (x: B.box a)
  : Lemma (requires mem h x \/ (wf left right h x /\ not (B.is_null x)))
          (ensures mem h x)
  = reveal_opaque (`%wf) (wf #a);
    if B.is_null x then () else
    FStar.Classical.move_requires (wf_step #a #unit (fun _ _ -> ()) left right h) x

/// A well-formed non-null pointer is a box of the heap, so the tree at it is a branch.
let wf_mem (#a: Type0) (left right: a -> B.box a) (h: heap a) (x: B.box a)
  : Lemma (requires wf left right h x /\ not (B.is_null x)) (ensures mem h x)
          [SMTPat (wf left right h x)]
  = mem_of_wf left right h x

/// R27.18. A child link of a node at a heap, `null` for a box the heap does not hold.
let link_at (#a: Type0) (link: a -> B.box a) (h: heap a) (x: B.box a) : B.box a =
  match lookup h x with
  | Some r -> link r
  | None -> B.null

let link_at_mem (#a: Type0) (link: a -> B.box a) (h: heap a) (x: B.box a)
  : Lemma (requires mem h x) (ensures link_at link h x == link (get h x))
          [SMTPat (link_at link h x)]
  = ()
