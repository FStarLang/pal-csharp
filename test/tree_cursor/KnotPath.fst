module KnotPath
#lang-pulse

/// The user's ownership predicate for `test/tree_cursor`: a **one-hole context** over the
/// `[Plain]` generic class `Knot<T>` declared in `Knot.cs`, together with the proof steps a
/// C# body takes when it descends through one.
///
/// `test/list_cursor` did this for a chain, where the walked part is a segment and the two
/// halves are `Take`/`Drop` of the counter. A tree gives neither for free, and the two
/// questions this file answers are exactly those two.
///
///   1. **What is the walked part?** The spine from the root down to the cursor, with each
///      node's off-path sibling subtree hanging off it. `knot_path` owns that spine and
///      `plug` fills the hole back in.
///
///   2. **How is it a function of a mutable local?** This is what decides whether a descent
///      lands inside R5.8's loop rule at all. The context of a descent is path-dependent, so
///      nothing like `Take` works. But the path a *search* takes is not a free choice: it is
///      determined by the tree and the key, both fixed for the whole loop. So the context
///      after `n` steps is `dctx t key n`, the subtree still to search is `dsub t key n`,
///      and `n` is a counter -- a mutable local, exactly as in the linear case.
///
/// `dctx`/`dsub` are to a descent what `Take`/`Drop` are to a walk, `plug` is what `Append`
/// is, and `path_close` is what `seg_close` is. A branching cursor needs no more loop
/// machinery than a linear one.
///
/// Pinned first, and independently, by `test/pulse_facts/TreeCursorFacts.fst`.

open Pulse
module B = Pulse.Lib.Box
module L = FStar.List.Tot
module T = Pulse.Lib.CSharp.Tree
module I32 = FStar.Int32

// ===========================================================================
// 2. The spec-level context, and the arithmetic of a descent
// ===========================================================================

/// The two children of a node, as *total* functions of the model. A specification that must
/// name a subtree before the heap has been read cannot use a projector: `Branch?._0` is
/// refined, and the refinement is not available where the term is typed. This is R15.7's
/// clamping rule again, one type up.
let subl (#a: Type0) (t: T.tree a) : T.tree a =
  match t with T.Leaf -> T.Leaf | T.Branch l _ _ -> l

let subr (#a: Type0) (t: T.tree a) : T.tree a =
  match t with T.Leaf -> T.Leaf | T.Branch _ _ r -> r

/// One step of the spine, seen from above: the entry at the node, the sibling subtree the
/// search did *not* enter, and which way it went. `FLeft e sib` reads "the search went left
/// here; `e` is the entry and `sib` the right subtree it left behind".
noeq type frame (a: Type0) =
  | FLeft  : T.kv a -> T.tree (T.kv a) -> frame a
  | FRight : T.tree (T.kv a) -> T.kv a -> frame a

/// Fill the hole. The list is **outermost first**, so the head frame is the root and
/// `plug` rebuilds the tree from the root down. That ordering is what makes a descent step
/// an `append` on the *right*, i.e. a `snoc`, which is the same shape as `seg_snoc`.
let rec plug (#a: Type0) (c: list (frame a)) (sub: T.tree (T.kv a))
  : Tot (T.tree (T.kv a)) (decreases c)
  = match c with
    | [] -> sub
    | FLeft e r :: rest -> T.Branch (plug rest sub) e r
    | FRight l e :: rest -> T.Branch l e (plug rest sub)

/// The subtree still to be searched after `n` steps of looking for `key`.
///
/// The recursion stops early on a hit, which is what makes the "found" case a *fixed point*
/// and so lets `dsub_kfind` below hold without a side condition. It terminates on the tree
/// rather than on `n`, which is what lets `n` be an unrefined `int` (R15.7).
let rec dsub (#a: Type0) (t: T.tree (T.kv a)) (key: int) (n: int)
  : Tot (T.tree (T.kv a)) (decreases t)
  = if n <= 0 then t
    else match t with
         | T.Leaf -> T.Leaf
         | T.Branch l e r ->
           if key < e.T.kv_key then dsub l key (n - 1)
           else if key > e.T.kv_key then dsub r key (n - 1)
           else t

/// The spine walked in those `n` steps, outermost first. Same recursion, same stopping rule.
let rec dctx (#a: Type0) (t: T.tree (T.kv a)) (key: int) (n: int)
  : Tot (list (frame a)) (decreases t)
  = if n <= 0 then []
    else match t with
         | T.Leaf -> []
         | T.Branch l e r ->
           if key < e.T.kv_key then FLeft e r :: dctx l key (n - 1)
           else if key > e.T.kv_key then FRight l e :: dctx r key (n - 1)
           else []

/// The two halves are complementary: plugging the unsearched subtree back into the spine
/// gives the tree back. This is `take_drop`, and it is why the walk can be given back.
let rec plug_dctx (#a: Type0) (t: T.tree (T.kv a)) (key: int) (n: int)
  : Lemma (ensures plug (dctx t key n) (dsub t key n) == t) (decreases t)
  = if n <= 0 then ()
    else match t with
         | T.Leaf -> ()
         | T.Branch l e r ->
           if key < e.T.kv_key then plug_dctx l key (n - 1)
           else if key > e.T.kv_key then plug_dctx r key (n - 1)
           else ()

/// Descending never changes the answer. This is the *correctness* half of a search, and it
/// needs no ordering hypothesis at all: `kfind` on a `Branch` is *defined* by comparing the
/// key with the entry, so following that comparison is following the definition. A search
/// tree that is out of order still gets the answer `kfind` says.
let rec dsub_kfind (#a: Type0) (t: T.tree (T.kv a)) (key: int) (n: int)
  : Lemma (ensures T.kfind (dsub t key n) key == T.kfind t key) (decreases t)
  = if n <= 0 then ()
    else match t with
         | T.Leaf -> ()
         | T.Branch l e r ->
           if key < e.T.kv_key then dsub_kfind l key (n - 1)
           else if key > e.T.kv_key then dsub_kfind r key (n - 1)
           else ()

/// The answer at the bottom: a search that runs off the end of the tree has established
/// that the key is not there. Stated as its own implication rather than left to the caller,
/// because `kfind` reduces only once the subtree is known to be `Leaf`.
let dsub_leaf_kfind (#a: Type0) (t: T.tree (T.kv a)) (key: int) (n: int)
  : Lemma (ensures dsub t key n == T.Leaf ==> T.kfind t key == None)
  = dsub_kfind t key n

/// The step, going left. Stated over the node's *parts* rather than over a projector,
/// because the C# caller has just read those parts out of the heap and can name them.
let rec dstep_left (#a: Type0) (t: T.tree (T.kv a)) (key: int) (n: int)
    (l: T.tree (T.kv a)) (e: T.kv a) (r: T.tree (T.kv a))
  : Lemma (requires 0 <= n /\ dsub t key n == T.Branch l e r /\ key < e.T.kv_key)
          (ensures  dsub t key (n + 1) == l /\
                    dctx t key (n + 1) == L.append (dctx t key n) [FLeft e r])
          (decreases t)
  = if n = 0 then ()
    else match t with
         | T.Leaf -> ()
         | T.Branch l0 e0 r0 ->
           if key < e0.T.kv_key then dstep_left l0 key (n - 1) l e r
           else if key > e0.T.kv_key then dstep_left r0 key (n - 1) l e r
           else ()

/// The step, going right.
let rec dstep_right (#a: Type0) (t: T.tree (T.kv a)) (key: int) (n: int)
    (l: T.tree (T.kv a)) (e: T.kv a) (r: T.tree (T.kv a))
  : Lemma (requires 0 <= n /\ dsub t key n == T.Branch l e r /\ key > e.T.kv_key)
          (ensures  dsub t key (n + 1) == r /\
                    dctx t key (n + 1) == L.append (dctx t key n) [FRight l e])
          (decreases t)
  = if n = 0 then ()
    else match t with
         | T.Leaf -> ()
         | T.Branch l0 e0 r0 ->
           if key < e0.T.kv_key then dstep_right l0 key (n - 1) l e r
           else if key > e0.T.kv_key then dstep_right r0 key (n - 1) l e r
           else ()

/// The measure. One descent step strictly shrinks the subtree left to search, which is what
/// a C# `Pal.Decreases` needs and what no counter alone could give -- a tree has no length.
let dsub_size_left (#a: Type0) (t: T.tree (T.kv a)) (key: int) (n: int)
    (l: T.tree (T.kv a)) (e: T.kv a) (r: T.tree (T.kv a))
  : Lemma (requires 0 <= n /\ dsub t key n == T.Branch l e r /\ key < e.T.kv_key)
          (ensures  T.size (dsub t key (n + 1)) < T.size (dsub t key n))
  = dstep_left t key n l e r

let dsub_size_right (#a: Type0) (t: T.tree (T.kv a)) (key: int) (n: int)
    (l: T.tree (T.kv a)) (e: T.kv a) (r: T.tree (T.kv a))
  : Lemma (requires 0 <= n /\ dsub t key n == T.Branch l e r /\ key > e.T.kv_key)
          (ensures  T.size (dsub t key (n + 1)) < T.size (dsub t key n))
  = dstep_right t key n l e r

// ===========================================================================
// 3. The two predicates
// ===========================================================================

/// A whole tree, rooted at `from`. This is what a `[Model]`-derived invariant would give at
/// arity two, written out by hand because §12 is where the user owns the predicate.
let rec knot_tree (#a: Type0) (p: perm)
                  ([@@@mkey] from: Class_Knot.class_Knot__opt a) (t: T.tree (T.kv a))
  : Tot slprop (decreases t)
  = match t with
    | T.Leaf -> pure (from == None)
    | T.Branch lt e rt ->
      exists* (v: Class_Knot.class_Knot a) (rc: Class_Knot.class_Knot__raw a).
        pure (from == Some v) **
        B.pts_to v #p rc **
        pure (e == T.entry (I32.v rc.fld_key) rc.fld_value) **
        knot_tree p rc.fld_left lt **
        knot_tree p rc.fld_right rt

/// The spine from `from` down to `to_`, with every off-path sibling owned along the way.
/// The recursion is on the *context*, not on a tree, which is what lets the two predicates
/// meet at an arbitrary point: `knot_path root cur c ** knot_tree cur sub` is a partition of
/// the same tree for every `c` and `sub` with `plug c sub == t`.
///
/// `[@@@mkey] from` is the emitter's annotation on a derived invariant's reference; here it
/// is what tells Pulse's matcher apart the spine (which starts at the root) from the subtree
/// (which starts at the cursor).
let rec knot_path (#a: Type0) (p: perm)
                  ([@@@mkey] from: Class_Knot.class_Knot__opt a) (to_: Class_Knot.class_Knot__opt a)
                  (c: list (frame a))
  : Tot slprop (decreases c)
  = match c with
    | [] -> pure (from == to_)
    | FLeft e sib :: rest ->
      exists* (v: Class_Knot.class_Knot a) (rc: Class_Knot.class_Knot__raw a).
        pure (from == Some v) **
        B.pts_to v #p rc **
        pure (e == T.entry (I32.v rc.fld_key) rc.fld_value) **
        knot_path p rc.fld_left to_ rest **
        knot_tree p rc.fld_right sib
    | FRight sib e :: rest ->
      exists* (v: Class_Knot.class_Knot a) (rc: Class_Knot.class_Knot__raw a).
        pure (from == Some v) **
        B.pts_to v #p rc **
        pure (e == T.entry (I32.v rc.fld_key) rc.fld_value) **
        knot_tree p rc.fld_left sib **
        knot_path p rc.fld_right to_ rest

/// The friendly names a C# `[SpecOp]` maps onto. Both `unfold`, so every lemma below applies
/// through them.
unfold
let holds (#a: Type0) (from: Class_Knot.class_Knot__opt a) (t: T.tree (T.kv a)) : slprop =
  knot_tree 1.0R from t

unfold
let spine (#a: Type0) (from to_: Class_Knot.class_Knot__opt a) (c: list (frame a)) : slprop =
  knot_path 1.0R from to_ c

// ===========================================================================
// 4. The structural lemmas
// ===========================================================================

/// The empty spine costs nothing.
ghost fn path_nil (#a: Type0) (x: Class_Knot.class_Knot__opt a)
  requires emp
  ensures  knot_path 1.0R x x ([] <: list (frame a))
{
  fold (knot_path 1.0R x x ([] <: list (frame a)));
}

/// The null test, as a statement about the *model*. §12 refuses to derive it and makes the
/// user state it; stated once, every descent that tests its cursor gets it by calling.
ghost fn tree_cases (#a: Type0) (from: Class_Knot.class_Knot__opt a) (t: T.tree (T.kv a))
  preserves knot_tree 1.0R from t
  ensures  pure ((Some? from <==> T.Branch? t) /\ (None? from ==> t == T.Leaf))
{
  match t {
    T.Leaf -> {
      unfold (knot_tree 1.0R from (T.Leaf <: T.tree (T.kv a)));
      fold (knot_tree 1.0R from (T.Leaf <: T.tree (T.kv a)));
    }
    T.Branch lt e rt -> {
      unfold (knot_tree 1.0R from (T.Branch lt e rt));
      with v rc. assert (B.pts_to v rc);
      fold (knot_tree 1.0R from (T.Branch lt e rt));
    }
  }
}

/// Two spines compose. This is `seg_append`, and like it, it is the only induction that
/// matters: everything a descent does is this lemma with the boundaries arranged
/// differently.
ghost fn rec path_append (#a: Type0)
    (head mid to_: Class_Knot.class_Knot__opt a) (c1 c2: list (frame a))
  requires knot_path 1.0R head mid c1 ** knot_path 1.0R mid to_ c2
  ensures  knot_path 1.0R head to_ (L.append c1 c2)
  decreases c1
{
  match c1 {
    Nil -> {
      unfold (knot_path 1.0R head mid ([] <: list (frame a)));
      rewrite (knot_path 1.0R mid to_ c2)
           as (knot_path 1.0R head to_ (L.append ([] <: list (frame a)) c2));
    }
    Cons f rest -> {
      match f {
        FLeft e sib -> {
          rewrite (knot_path 1.0R head mid c1)
               as (knot_path 1.0R head mid (FLeft e sib :: rest));
          unfold (knot_path 1.0R head mid (FLeft e sib :: rest));
          with v rc. assert (B.pts_to v #1.0R rc);
          path_append rc.fld_left mid to_ rest c2;
          fold (knot_path 1.0R head to_ (FLeft e sib :: L.append rest c2));
          rewrite (knot_path 1.0R head to_ (FLeft e sib :: L.append rest c2))
               as (knot_path 1.0R head to_ (L.append c1 c2));
        }
        FRight sib e -> {
          rewrite (knot_path 1.0R head mid c1)
               as (knot_path 1.0R head mid (FRight sib e :: rest));
          unfold (knot_path 1.0R head mid (FRight sib e :: rest));
          with v rc. assert (B.pts_to v #1.0R rc);
          path_append rc.fld_right mid to_ rest c2;
          fold (knot_path 1.0R head to_ (FRight sib e :: L.append rest c2));
          rewrite (knot_path 1.0R head to_ (FRight sib e :: L.append rest c2))
               as (knot_path 1.0R head to_ (L.append c1 c2));
        }
      }
    }
  }
}

/// Fill the hole back in. `seg_close`'s counterpart, and, like it, the step a C# body takes
/// when it leaves the descent -- at the bottom or on a hit, it makes no difference.
ghost fn rec path_close (#a: Type0)
    (head from: Class_Knot.class_Knot__opt a) (c: list (frame a)) (sub: T.tree (T.kv a))
  requires knot_path 1.0R head from c ** knot_tree 1.0R from sub
  ensures  knot_tree 1.0R head (plug c sub)
  decreases c
{
  match c {
    Nil -> {
      unfold (knot_path 1.0R head from ([] <: list (frame a)));
      rewrite (knot_tree 1.0R from sub)
           as (knot_tree 1.0R head (plug ([] <: list (frame a)) sub));
    }
    Cons f rest -> {
      match f {
        FLeft e sib -> {
          rewrite (knot_path 1.0R head from c)
               as (knot_path 1.0R head from (FLeft e sib :: rest));
          unfold (knot_path 1.0R head from (FLeft e sib :: rest));
          with v rc. assert (B.pts_to v #1.0R rc);
          path_close rc.fld_left from rest sub;
          fold (knot_tree 1.0R head (T.Branch (plug rest sub) e sib));
          rewrite (knot_tree 1.0R head (T.Branch (plug rest sub) e sib))
               as (knot_tree 1.0R head (plug c sub));
        }
        FRight sib e -> {
          rewrite (knot_path 1.0R head from c)
               as (knot_path 1.0R head from (FRight sib e :: rest));
          unfold (knot_path 1.0R head from (FRight sib e :: rest));
          with v rc. assert (B.pts_to v #1.0R rc);
          path_close rc.fld_right from rest sub;
          fold (knot_tree 1.0R head (T.Branch sib e (plug rest sub)));
          rewrite (knot_tree 1.0R head (T.Branch sib e (plug rest sub)))
               as (knot_tree 1.0R head (plug c sub));
        }
      }
    }
  }
}

// ===========================================================================
// 5. The C# face: one lemma per step a C# descent takes
// ===========================================================================

/// A node whose four fields have been read out. `CursorFacts`'s `opened` at arity four: it
/// names the cursor the invariant talks about, the box a field access reads through, and the
/// four field *values* the C# body is about to bind to locals.
///
/// The two subtrees are `subl`/`subr` of `sub` rather than two existentials, and that is not
/// cosmetic. An existential would leave Pulse's matcher with two `knot_tree` goals whose only
/// distinguishing argument is a pointer it has just learned by *reading the heap*, and it
/// declines to guess between them. Making the model half of each conjunct a function of the
/// subtree the invariant already names tells the two apart syntactically, and the pointer is
/// then settled by the `mkey`. The linear case never met this because a cell has one child.
unfold
let knot_open (#a: Type0)
    (from: Class_Knot.class_Knot__opt a) (v: Class_Knot.class_Knot a)
    (k: I32.t) (value: a) (lp rp: Class_Knot.class_Knot__opt a)
    (sub: T.tree (T.kv a))
  : slprop
  = B.pts_to v ({ Class_Knot.fld_key = k; Class_Knot.fld_value = value; Class_Knot.fld_left = lp; Class_Knot.fld_right = rp }) **
    knot_tree 1.0R lp (subl sub) **
    knot_tree 1.0R rp (subr sub) **
    pure (from == Some v /\
          sub == T.Branch (subl sub) (T.entry (I32.v k) value) (subr sub))

/// `knot_open` with the *machine* key hidden, which is the only form a C# contract can name:
/// R4.13 sends a C# `int` into a specification as its `.v`, so a C# `[Requires]` cannot write
/// an `I32.t` at all. Hiding it costs nothing -- it is determined by the `pts_to`, so the
/// matcher recovers it -- and it buys the whole C# face, because the key a step compares
/// against is then read off the *model* (`node_key`) rather than passed in as a machine
/// value. This is R4.13's convention at one remove: `DllSeg.cell` does the same thing for a
/// node's payload, and a search tree needs it for the field it is *ordered* by.
unfold
let knot_opened (#a: Type0)
    (from: Class_Knot.class_Knot__opt a) (v: Class_Knot.class_Knot a)
    (value: a) (lp rp: Class_Knot.class_Knot__opt a)
    (sub: T.tree (T.kv a))
  : slprop
  = exists* (k: I32.t). knot_open from v k value lp rp sub

/// The shape a C# `[Ensures]` can name: the four field values still existential, because a
/// C# postcondition cannot bind one and because the body is about to produce them by
/// *reading the fields*. `unfold` means Pulse eliminates the four at the call site.
unfold
let knot_open_some (#a: Type0)
    (from: Class_Knot.class_Knot__opt a) (v: Class_Knot.class_Knot a) (sub: T.tree (T.kv a))
  : slprop
  = exists* (value: a) (lp rp: Class_Knot.class_Knot__opt a).
      knot_opened from v value lp rp sub

/// The ownership a freshly allocated node has, over the four field values a C#
/// `new Knot<T> { ... }` supplies (R12.4).
unfold
let knot_held (#a: Type0) (v: Class_Knot.class_Knot a)
    (k: int) (value: a) (lp rp: Class_Knot.class_Knot__opt a)
  : slprop
  = exists* (x: I32.t).
    B.pts_to v ({ Class_Knot.fld_key = x; Class_Knot.fld_value = value; Class_Knot.fld_left = lp; Class_Knot.fld_right = rp }) **
    pure (I32.v x == k)

/// The empty tree. A null reference denotes `Leaf`, and saying so is the user's job: §12
/// gives them the predicate, so it gives them its base case too.
ghost fn tree_empty (#a: Type0) (unit_arg: unit)
  requires emp
  ensures  knot_tree 1.0R (None #(Class_Knot.class_Knot a)) (T.Leaf <: T.tree (T.kv a))
{
  fold (knot_tree 1.0R (None #(Class_Knot.class_Knot a)) (T.Leaf <: T.tree (T.kv a)));
}

/// Build a node from two trees the caller owns outright. The descent needs something to
/// descend through, and this is the only place a `[Plain]` allocation meets the predicate.
ghost fn tree_node (#a: Type0) (v: Class_Knot.class_Knot a)
    (k: int) (value: a) (lp rp: Class_Knot.class_Knot__opt a) (lt rt: T.tree (T.kv a))
  requires knot_held v k value lp rp ** knot_tree 1.0R lp lt ** knot_tree 1.0R rp rt
  ensures  knot_tree 1.0R (Some v) (T.Branch lt (T.entry k value) rt)
{
  fold (knot_tree 1.0R (Some v) (T.Branch lt (T.entry k value) rt));
}

/// `kget` at a key the map does not hold. The `match` is what makes it go through without
/// an inversion axiom: it is case analysis on the very `option` `kget` scrutinises.
let kget_absent (#a: Type0) (t: T.tree (T.kv a)) (key: int) (dflt: a)
  : Lemma (requires T.khas t key == false) (ensures T.kget t key dflt == dflt)
  = match T.kfind t key with
    | None -> ()
    | Some _ -> ()

/// Start the descent. `dctx t key 0` is empty and `dsub t key 0` is the whole tree, so the
/// loop is entered with the cursor at the root and the counter at zero and the invariant
/// holds by construction.
ghost fn tree_start (#a: Type0) (root: Class_Knot.class_Knot__opt a) (key: int) (t: T.tree (T.kv a))
  requires knot_tree 1.0R root t
  ensures  knot_path 1.0R root root (dctx t key 0) ** knot_tree 1.0R root (dsub t key 0)
{
  path_nil root;
  rewrite (knot_path 1.0R root root ([] <: list (frame a)))
       as (knot_path 1.0R root root (dctx t key 0));
  rewrite (knot_tree 1.0R root t)
       as (knot_tree 1.0R root (dsub t key 0));
}

/// The loop condition. `tree_cases` ties the null test to the *shape* of the remaining
/// subtree; this ties it to the counter, and reports the answer at the bottom -- which is
/// what lets a C# body conclude, from `cur == null` alone, that the key is not there.
ghost fn tree_at_end (#a: Type0)
    (from: Class_Knot.class_Knot__opt a) (key: int) (n: int) (t: T.tree (T.kv a))
  preserves knot_tree 1.0R from (dsub t key n)
  ensures  pure ((None? from <==> dsub t key n == T.Leaf) /\
                 (None? from ==> T.khas t key == false))
{
  dsub_leaf_kfind t key n;
  tree_cases from (dsub t key n);
}

/// Open the node at the cursor, so that its four fields can be read.
ghost fn tree_open (#a: Type0)
    (from: Class_Knot.class_Knot__opt a) (v: Class_Knot.class_Knot a) (sub: T.tree (T.kv a))
  requires knot_tree 1.0R from sub ** pure (T.Branch? sub /\ from == Some v)
  ensures  knot_open_some from v sub
{
  rewrite (knot_tree 1.0R from sub)
       as (knot_tree 1.0R from (T.Branch (subl sub) (T.Branch?._1 sub) (subr sub)));
  unfold (knot_tree 1.0R from (T.Branch (subl sub) (T.Branch?._1 sub) (subr sub)));
  with w rc. assert (B.pts_to w #1.0R rc);
  rewrite each w as v;
  rewrite (B.pts_to v #1.0R rc)
       as (B.pts_to v ({ Class_Knot.fld_key = rc.fld_key; Class_Knot.fld_value = rc.fld_value;
                         Class_Knot.fld_left = rc.fld_left; Class_Knot.fld_right = rc.fld_right }));
  fold (knot_open from v (rc.fld_key) rc.fld_value rc.fld_left rc.fld_right sub);
}

/// The key at the root of a subtree, as a *total* function of the model -- `subl`/`subr` one
/// field over. This is what lets a C# `[Requires]` state which way a step went without ever
/// naming a machine integer: the guard a descent tests is `key < node_key sub`, and the C#
/// body's own `key < nk` implies it because `knot_open` ties the field to the model.
let node_key (#a: Type0) (t: T.tree (T.kv a)) : int =
  match t with
  | T.Branch _ e _ -> e.T.kv_key
  | T.Leaf -> 0

/// The hit. The node at the cursor carries the key, so the value read out of it is the
/// answer -- and the node is closed straight back up, because a hit ends the descent.
ghost fn tree_found (#a: Type0)
    (from: Class_Knot.class_Knot__opt a) (v: Class_Knot.class_Knot a)
    (value: a) (lp rp: Class_Knot.class_Knot__opt a)
    (key: int) (n: int) (dflt: a) (t: T.tree (T.kv a))
  requires knot_opened from v value lp rp (dsub t key n) **
           pure (key == node_key (dsub t key n))
  ensures  knot_tree 1.0R from (dsub t key n) **
           pure (T.kget t key dflt == value /\ T.khas t key == true)
{
  with k. assert (knot_open from v k value lp rp (dsub t key n));
  unfold (knot_open from v k value lp rp (dsub t key n));
  dsub_kfind t key n;
  tree_node v (I32.v k) value lp rp (subl (dsub t key n)) (subr (dsub t key n));
  rewrite (knot_tree 1.0R (Some v)
             (T.Branch (subl (dsub t key n)) (T.entry (I32.v k) value) (subr (dsub t key n))))
       as (knot_tree 1.0R from (dsub t key n));
}

/// The step, going left: the node at the cursor joins the spine and the cursor moves to its
/// left child. `dstep_left` says the same thing about the model, and `path_append` moves the
/// ownership; nothing else happens.
ghost fn tree_left (#a: Type0)
    (root from: Class_Knot.class_Knot__opt a) (v: Class_Knot.class_Knot a)
    (value: a) (lp rp: Class_Knot.class_Knot__opt a)
    (key: int) (n: int) (t: T.tree (T.kv a))
  requires knot_path 1.0R root from (dctx t key n) **
           knot_opened from v value lp rp (dsub t key n) **
           pure (0 <= n /\ key < node_key (dsub t key n))
  ensures  knot_path 1.0R root lp (dctx t key (n + 1)) **
           knot_tree 1.0R lp (dsub t key (n + 1)) **
           pure (0 <= n ==> T.size (dsub t key (n + 1)) < T.size (dsub t key n))
{
  with k. assert (knot_open from v k value lp rp (dsub t key n));
  unfold (knot_open from v k value lp rp (dsub t key n));
  dstep_left t key n (subl (dsub t key n)) (T.entry (I32.v k) value) (subr (dsub t key n));
  path_nil lp;
  fold (knot_path 1.0R from lp
          (FLeft (T.entry (I32.v k) value) (subr (dsub t key n)) :: ([] <: list (frame a))));
  path_append root from lp (dctx t key n)
    [FLeft (T.entry (I32.v k) value) (subr (dsub t key n))];
  rewrite (knot_path 1.0R root lp
             (L.append (dctx t key n) [FLeft (T.entry (I32.v k) value) (subr (dsub t key n))]))
       as (knot_path 1.0R root lp (dctx t key (n + 1)));
  rewrite (knot_tree 1.0R lp (subl (dsub t key n)))
       as (knot_tree 1.0R lp (dsub t key (n + 1)));
}

/// The step, going right.
ghost fn tree_right (#a: Type0)
    (root from: Class_Knot.class_Knot__opt a) (v: Class_Knot.class_Knot a)
    (value: a) (lp rp: Class_Knot.class_Knot__opt a)
    (key: int) (n: int) (t: T.tree (T.kv a))
  requires knot_path 1.0R root from (dctx t key n) **
           knot_opened from v value lp rp (dsub t key n) **
           pure (0 <= n /\ key > node_key (dsub t key n))
  ensures  knot_path 1.0R root rp (dctx t key (n + 1)) **
           knot_tree 1.0R rp (dsub t key (n + 1)) **
           pure (0 <= n ==> T.size (dsub t key (n + 1)) < T.size (dsub t key n))
{
  with k. assert (knot_open from v k value lp rp (dsub t key n));
  unfold (knot_open from v k value lp rp (dsub t key n));
  dstep_right t key n (subl (dsub t key n)) (T.entry (I32.v k) value) (subr (dsub t key n));
  path_nil rp;
  fold (knot_path 1.0R from rp
          (FRight (subl (dsub t key n)) (T.entry (I32.v k) value) :: ([] <: list (frame a))));
  path_append root from rp (dctx t key n)
    [FRight (subl (dsub t key n)) (T.entry (I32.v k) value)];
  rewrite (knot_path 1.0R root rp
             (L.append (dctx t key n) [FRight (subl (dsub t key n)) (T.entry (I32.v k) value)]))
       as (knot_path 1.0R root rp (dctx t key (n + 1)));
  rewrite (knot_tree 1.0R rp (subr (dsub t key n)))
       as (knot_tree 1.0R rp (dsub t key (n + 1)));
}

/// Give the tree back, from wherever the descent stopped. `path_close` plus `plug_dctx`, and
/// nothing else -- which is the point: the two halves compose at *every* point on the path,
/// so a search that stops early pays exactly one lemma call for doing so.
ghost fn tree_close (#a: Type0)
    (root from: Class_Knot.class_Knot__opt a) (key: int) (n: int) (t: T.tree (T.kv a))
  requires knot_path 1.0R root from (dctx t key n) ** knot_tree 1.0R from (dsub t key n)
  ensures  knot_tree 1.0R root t
{
  path_close root from (dctx t key n) (dsub t key n);
  plug_dctx t key n;
  rewrite (knot_tree 1.0R root (plug (dctx t key n) (dsub t key n)))
       as (knot_tree 1.0R root t);
}

