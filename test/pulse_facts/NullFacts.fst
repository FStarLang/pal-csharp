module NullFacts
#lang-pulse

/// §0 probe for the *box-as-nullable* encoding of a C# reference.
///
/// Today §10 emits three types for a recursive class:
///
/// ```
/// noeq type class_Node__raw = { …; fld_next: class_Node__opt }
/// and class_Node     = B.box class_Node__raw
/// and class_Node__opt = option class_Node
/// ```
///
/// The `option` is a second nullability layer on top of one Pulse already has:
/// `Pulse.Lib.Box` declares `null`, `is_null r : b:bool{b <==> r == null}`, and
/// `pts_to_not_null`. So a `box` *is* a nullable pointer, and wrapping it in `option`
/// makes `Node` and `Node?` two **different types** — which is where every `Some?.v`,
/// every `rewrite each v as (Some?.v x)`, the `as_opt` lemma and the duplicate
/// `intro`/`intro_cons` pair come from. None of them say anything; they are all the cost
/// of a coercion between two representations of the same pointer.
///
/// What this file probes is the encoding C# actually has: **one type, and non-nullness is
/// a refinement.**
///
/// ```
/// class_Node__opt = B.box class_Node__raw
/// class_Node      = b: class_Node__opt { not (B.is_null b) }
/// ```
///
/// `class_Node <: class_Node__opt` is then ordinary F* refinement subtyping, so a
/// non-nullable reference is usable wherever a nullable one is with **no coercion at
/// all**, and the direction that needs a proof — nullable to non-null — is exactly the one
/// a C# null test provides.
///
/// The questions, in order:
///
///   N1  Does the recursive record still form with `box` in place of `option box`?
///   N2  Does the inductive invariant still work, with one fewer existential?
///   N3  Do all eight case lemmas still go through, and which of them survive at all?
///   N4  Does the recursive share/gather still go through?
///   N5  Does a read-only traversal still verify?
///   N6  Does a *destructive* traversal still verify (F39)?
///   N7  Does a §12-style segment predicate get simpler — specifically, does it lose the
///       `pure (from == Some v)` conjunct that F73 says makes a binder unsolvable?

open Pulse
module B = Pulse.Lib.Box
module I32 = FStar.Int32
module T = FStar.Tactics

/// ---------------------------------------------------------------------------
/// N1. The types.
///
/// Note what is *not* here: no `and`. The mutual group existed only to let `raw` mention
/// `class_Node__opt`, which had to be named before it could be wrapped in `option`. With
/// the box used directly the record refers to `B.box` and nothing else, so the group
/// collapses to a single `noeq type` and two abbreviations.
/// ---------------------------------------------------------------------------

noeq type class_Node__raw = {
  fld_value: I32.t;
  fld_next: B.box class_Node__raw;
}

let class_Node__opt = B.box class_Node__raw

/// A C# `Node` — non-nullable. A *subtype* of `Node?`, which is what makes every coercion
/// in the current scheme disappear rather than move.
let class_Node = b: class_Node__opt { not (B.is_null b) }

let class_Node__model = list int

/// ---------------------------------------------------------------------------
/// N2. The invariant.
///
/// Compare with what §10 emits today:
///
/// ```
/// | Cons m0 m1 ->
///   exists* (v: class_Node) (r: class_Node__raw).
///     pure (x == Some v) ** B.pts_to v #p r ** … 
/// ```
///
/// Two binders, one of which (`v`) is reachable *only* through a `pure` — which is the
/// exact shape F73 records as unsolvable by Pulse's matcher when such a predicate has to
/// be folded. Here there is one binder, it is the record, and it is determined by the
/// `pts_to` the matcher is looking at anyway.
/// ---------------------------------------------------------------------------

let rec class_Node__inv_opt ([@@@mkey] x: class_Node__opt) (p: perm) (m: class_Node__model)
  : Tot slprop (decreases m)
  = match m with
    | Nil -> pure (x == B.null)
    | Cons m0 m1 ->
      exists* (r: class_Node__raw).
        B.pts_to x #p r **
        pure (m0 == (I32.v r.fld_value)) **
        class_Node__inv_opt r.fld_next p m1

/// The non-nullable invariant is the *same function*, applied to a `this` that coerces up.
/// Today this is `class_Node__inv_opt (Some this) p m`, and the `Some` is what every
/// `as_opt`/`intro`/`inv_share`/`inv_gather` rewrite is undoing.
let class_Node__inv (this: class_Node) (#[T.exact (`1.0R)] p: perm) (m: class_Node__model)
  : slprop
  = class_Node__inv_opt this p m

/// The fact the `option` layer was buying: a **non-nullable** reference cannot have the
/// empty model. It survives, and for a better reason than before — `Some this =!= None`
/// was a fact about the encoding, `not (is_null this)` is the refinement C# itself wrote.
ghost fn nonnull_is_cons (this: class_Node) (#p: perm) (#m: class_Node__model)
  preserves class_Node__inv this #p m
  ensures  pure (Cons? m)
{
  match m {
    Nil -> {
      rewrite (class_Node__inv this #p m) as (class_Node__inv_opt this p Nil);
      unfold (class_Node__inv_opt this p Nil);
      fold (class_Node__inv_opt this p Nil);
      rewrite (class_Node__inv_opt this p Nil) as (class_Node__inv this #p m);
    }
    Cons m0 m1 -> { () }
  }
}

/// ---------------------------------------------------------------------------
/// N3. The case lemmas.
/// ---------------------------------------------------------------------------

/// `cases`. The Cons branch is the one place the encoding costs a step it did not cost
/// before: `Some? x` was true *definitionally*, whereas `not (is_null x)` has to be got
/// from the `pts_to`. `B.pts_to_not_null` is that step, and it is a library lemma.
ghost fn class_Node__cases (x: class_Node__opt) (#p: perm) (#m: class_Node__model)
  preserves class_Node__inv_opt x p m
  ensures pure (not (B.is_null x) <==> Cons? m)
{
  match m {
    Nil -> {
      unfold (class_Node__inv_opt x p Nil);
      fold (class_Node__inv_opt x p Nil);
    }
    Cons m0 m1 -> {
      unfold (class_Node__inv_opt x p (Cons m0 m1));
      B.pts_to_not_null x;
      fold (class_Node__inv_opt x p (Cons m0 m1));
    }
  }
}

ghost fn class_Node__nil_case (x: class_Node__opt) (#p: perm) (#m: class_Node__model)
  preserves class_Node__inv_opt x p m
  requires pure (B.is_null x)
  ensures  pure (m == Nil)
{
  match m {
    Nil -> { () }
    Cons m0 m1 -> {
      unfold (class_Node__inv_opt x p (Cons m0 m1));
      B.pts_to_not_null x;
      unreachable ()
    }
  }
}

ghost fn class_Node__elim_nil (x: class_Node__opt) (#p: perm) (#m: class_Node__model)
  requires class_Node__inv_opt x p m ** pure (B.is_null x)
  ensures  pure (m == Nil)
{
  class_Node__nil_case x;
  unfold (class_Node__inv_opt x p Nil);
}

ghost fn class_Node__intro_nil (x: class_Node__opt) (p: perm)
  requires pure (x == B.null)
  ensures  class_Node__inv_opt x p Nil
{
  fold (class_Node__inv_opt x p Nil)
}

/// `elim_cons`. Its parameter's refinement *is* `class_Node`, so the signature says what
/// the current one says with `{ Some? x }` — and the body loses the `with v r.` /
/// `rewrite each v as (Some?.v x)` dance, because there is no `v`.
ghost fn class_Node__elim_cons (x: class_Node) (#p: perm) (#m: class_Node__model)
  requires class_Node__inv_opt x p m
  ensures exists* (r: class_Node__raw) (m1: class_Node__model).
    B.pts_to x #p r **
    class_Node__inv_opt r.fld_next p m1 **
    pure (m == Cons (I32.v r.fld_value) m1)
{
  match m {
    Nil -> {
      unfold (class_Node__inv_opt x p Nil);
      unreachable ()
    }
    Cons m0 m1 -> {
      unfold (class_Node__inv_opt x p (Cons m0 m1));
      ()
    }
  }
}

/// `intro_cons`. And this is `intro` as well: today they are two lemmas because one takes
/// a `class_Node__opt { Some? x }` and the other a `class_Node`, which were different
/// types. They are now the same type, so this is one lemma and `class_Node__intro` and
/// `class_Node__as_opt` can both be **deleted**.
ghost fn class_Node__intro_cons (x: class_Node)
    (#p: perm) (#r: class_Node__raw) (#m1: class_Node__model)
  requires B.pts_to x #p r **
           class_Node__inv_opt r.fld_next p m1
  ensures  class_Node__inv_opt x p (Cons (I32.v r.fld_value) m1)
{
  fold (class_Node__inv_opt x p (Cons (I32.v r.fld_value) m1))
}

/// ---------------------------------------------------------------------------
/// N4. Recursive share and gather.
/// ---------------------------------------------------------------------------

ghost fn rec class_Node__inv_opt_share (x: class_Node__opt) (#p: perm) (#m: class_Node__model)
  requires class_Node__inv_opt x p m
  ensures  class_Node__inv_opt x (p /. 2.0R) m ** class_Node__inv_opt x (p /. 2.0R) m
  decreases m
{
  class_Node__cases x;
  if (B.is_null x) {
    class_Node__elim_nil x;
    class_Node__intro_nil x (p /. 2.0R);
    class_Node__intro_nil x (p /. 2.0R);
  } else {
    class_Node__elim_cons x;
    with r m1. assert (B.pts_to x #p r ** class_Node__inv_opt r.fld_next p m1);
    B.share x;
    class_Node__inv_opt_share r.fld_next #p #m1;
    class_Node__intro_cons x #(p /. 2.0R) #r #m1;
    class_Node__intro_cons x #(p /. 2.0R) #r #m1;
  }
}

[@@allow_ambiguous]
ghost fn rec class_Node__inv_opt_gather (x: class_Node__opt) (p q: perm)
    (#m #alt_m: class_Node__model)
  requires class_Node__inv_opt x p m ** class_Node__inv_opt x q alt_m
  ensures  class_Node__inv_opt x (p +. q) m ** pure (m == alt_m)
  decreases m
{
  class_Node__cases x #p #m;
  class_Node__cases x #q #alt_m;
  if (B.is_null x) {
    class_Node__elim_nil x #p #m;
    class_Node__elim_nil x #q #alt_m;
    class_Node__intro_nil x (p +. q);
  } else {
    class_Node__elim_cons x #p #m;
    with r m1. assert (B.pts_to x #p r ** class_Node__inv_opt r.fld_next p m1);
    class_Node__elim_cons x #q #alt_m;
    with alt_r alt_m1. assert (B.pts_to x #q alt_r ** class_Node__inv_opt alt_r.fld_next q alt_m1);
    B.gather x;
    rewrite each alt_r as r;
    class_Node__inv_opt_gather r.fld_next p q #m1 #alt_m1;
    class_Node__intro_cons x #(p +. q) #r #m1;
  }
}

/// The `inv` wrappers. Today each clause is rewritten through `(Some this)`; here the
/// rewrite is still needed — `class_Node__inv` is an ordinary `let`, so Pulse does not see
/// through it — but it rewrites `inv` to `inv_opt` at the *same* argument, with no `Some`
/// to introduce and none to discharge.
ghost fn class_Node__inv_share (this: class_Node) (#p: perm) (#m: class_Node__model)
  requires class_Node__inv this #p m
  ensures  class_Node__inv this #(p /. 2.0R) m ** class_Node__inv this #(p /. 2.0R) m
{
  rewrite (class_Node__inv this #p m) as (class_Node__inv_opt this p m);
  class_Node__inv_opt_share this;
  rewrite (class_Node__inv_opt this (p /. 2.0R) m) as (class_Node__inv this #(p /. 2.0R) m);
  rewrite (class_Node__inv_opt this (p /. 2.0R) m) as (class_Node__inv this #(p /. 2.0R) m);
}

[@@allow_ambiguous]
ghost fn class_Node__inv_gather_gen (this: class_Node) (p q: perm) (#m #alt_m: class_Node__model)
  requires class_Node__inv this #p m ** class_Node__inv this #q alt_m
  ensures  class_Node__inv this #(p +. q) m ** pure (m == alt_m)
{
  rewrite (class_Node__inv this #p m) as (class_Node__inv_opt this p m);
  rewrite (class_Node__inv this #q alt_m) as (class_Node__inv_opt this q alt_m);
  class_Node__inv_opt_gather this p q;
  rewrite (class_Node__inv_opt this (p +. q) m) as (class_Node__inv this #(p +. q) m);
}

/// ---------------------------------------------------------------------------
/// N5. A read-only traversal, in R10.7's shape — a null test opening the window.
/// ---------------------------------------------------------------------------

fn rec func_Lists_Length (var_x: class_Node__opt) (#p: perm) (#m: erased class_Node__model)
  requires class_Node__inv_opt var_x p m **
           pure (List.Tot.length (reveal m) < 2147483647)
  returns  var_result: I32.t
  ensures  class_Node__inv_opt var_x p m **
           pure (I32.v var_result == List.Tot.length (reveal m))
  decreases (reveal m)
{
  class_Node__cases var_x;
  if (B.is_null var_x) {
    class_Node__nil_case var_x;
    0l
  } else {
    class_Node__elim_cons var_x;
    let t1 = B.op_Bang var_x;
    let t0 = func_Lists_Length t1.fld_next;
    let t2 = (I32.add 1l t0);
    class_Node__intro_cons var_x;
    t2
  }
}

/// ---------------------------------------------------------------------------
/// N6. A destructive traversal — F39, the field write inside the window.
/// ---------------------------------------------------------------------------

fn rec func_Lists_Bump (var_x: class_Node__opt) (#m: erased class_Node__model)
  requires class_Node__inv_opt var_x 1.0R m
  ensures  exists* (post: class_Node__model).
             class_Node__inv_opt var_x 1.0R post **
             pure (List.Tot.length post == List.Tot.length (reveal m))
  decreases (reveal m)
{
  class_Node__cases var_x;
  if (B.is_null var_x) {
    class_Node__nil_case var_x;
    ()
  } else {
    class_Node__elim_cons var_x;
    with r m1. assert (B.pts_to var_x #1.0R r ** class_Node__inv_opt r.fld_next 1.0R m1);
    let node = B.op_Bang var_x;
    func_Lists_Bump node.fld_next;
    with m1'. assert (class_Node__inv_opt node.fld_next 1.0R m1');
    B.op_Colon_Equals var_x ({ node with fld_value = 0l });
    class_Node__intro_cons var_x #1.0R #({ node with fld_value = 0l }) #m1';
  }
}

/// ---------------------------------------------------------------------------
/// N7. A §12-style segment predicate — the shape `test/dll_segment`, `test/list_cursor`
/// and `test/tree_cursor` are written in.
///
/// Today a user writes the cons case as
///
/// ```
/// | hd :: tl -> exists* v r. pure (from == Some v) ** B.pts_to v #p r ** …
/// ```
///
/// and `v` is a binder reachable *only* through a `pure`, which F73 says the matcher
/// cannot solve — the reason `KnotPath.knot_open` had to keep an explicit machine field
/// and hide it behind a second wrapper (R16.3). With the box used directly the binder is
/// simply not there: `from` *is* the pointer.
/// ---------------------------------------------------------------------------

let rec seg (p: perm) ([@@@mkey] from: class_Node__opt) (to_: class_Node__opt) (l: list int)
  : Tot slprop (decreases l)
  = match l with
    | [] -> pure (from == to_)
    | hd :: tl ->
      exists* (r: class_Node__raw).
        B.pts_to from #p r **
        pure (hd == I32.v r.fld_value) **
        seg p r.fld_next to_ tl

/// `snoc` — the step an iterative cursor takes (§16). This is the lemma to compare, because
/// `CellSeg.seg_snoc` is the same statement under the option encoding:
///
/// ```
/// ghost fn seg_snoc (head from: class_Cell__opt a) (v: class_Cell a)
///                   (value: a) (next: class_Cell__opt a) (l: list a)
///   requires cell_seg 1.0R head from l ** B.pts_to v ({…}) ** pure (from == Some v)
/// ```
///
/// Two parameters for one pointer, a `pure` tying them together, and a `rewrite (cell_seg …
/// (Some v) …) as (cell_seg … from …)` in the body to undo it. Here `at` *is* the pointer,
/// so there is one parameter, no `pure`, and no rewrite — and no binder trapped behind a
/// `pure` for F73 to bite.
ghost fn rec seg_snoc (p: perm) (from: class_Node__opt) (at: class_Node)
    (#l: list int) (#r: class_Node__raw)
  requires seg p from at l ** B.pts_to at #p r
  ensures  seg p from r.fld_next (List.Tot.append l [I32.v r.fld_value])
  decreases l
{
  match l {
    Nil -> {
      unfold (seg p from at Nil);
      fold (seg p r.fld_next r.fld_next ([] <: list int));
      fold (seg p at r.fld_next [I32.v r.fld_value]);
      rewrite (seg p at r.fld_next [I32.v r.fld_value])
           as (seg p from r.fld_next (List.Tot.append (Nil <: list int) [I32.v r.fld_value]));
    }
    Cons hd tl -> {
      unfold (seg p from at (Cons hd tl));
      with rr. assert (B.pts_to from #p rr);
      seg_snoc p rr.fld_next at #tl #r;
      fold (seg p from r.fld_next (Cons hd (List.Tot.append tl [I32.v r.fld_value])));
    }
  }
}
