module GenericClassFacts

/// Pinned facts for *generic* recursive classes (doc/translation.md §15).
///
/// This is the §0 probe for M9. `RecursiveFacts` pinned the shape of a recursive class's
/// ownership predicate at a fixed element type; the question here is the one M8 left open
/// and deliberately refused (PALCS0581): what happens to that shape when the class itself
/// is parameterised by a type.
///
/// The text below is exactly the emitted `Class_Node.fst` of `test/linked_list`, with one
/// change applied uniformly: a type parameter. Nothing else is touched. If it verifies,
/// then generic classes cost the emitter binders and applications and nothing more — the
/// same answer M8 got for methods.
///
/// The one design question the probe is here to settle is *which binders are implicit*.

open Pulse

module B = Pulse.Lib.Box
module I32 = FStar.Int32
module L = FStar.List.Tot
module T = FStar.Tactics

#lang-pulse

// ===========================================================================
// F66. A mutually recursive type group may be parameterised.
// ===========================================================================

/// The three declarations R10.1 ties together — the record, the `box` abbreviation and the
/// nullable abbreviation — each repeat the binder. That is F*'s rule for a `type … and …`
/// group and it is the only syntactic accommodation generics ask of §10.
///
/// The parameter is on the *value* field. The recursive field is `class_Node__opt a`: the
/// recursion is at the same type argument, which is what makes the group well founded and
/// is also all a C# `Node<T>` can say — `Node<T>.next` is a `Node<T>?`, never a `Node<U>?`.
noeq type class_Node__raw (a: Type0) = {
  fld_value: a;
  fld_next: class_Node__opt a;
}
and class_Node (a: Type0) = B.box (class_Node__raw a)
and class_Node__opt (a: Type0) = option (class_Node a)

// ===========================================================================
// F67. The model type is parameterised, and its refinement travels with it.
// ===========================================================================

/// R3.9d's model refinement is a predicate on the model, so it is parameterised exactly as
/// the model is. `True` here stands for "no [Refine] was written", which is the emitter's
/// own degenerate case.
let class_Node__model__pred (#a: Type0) (m: list a) : prop =
  True

type class_Node__model (a: Type0) = m: list a { class_Node__model__pred m }

// ===========================================================================
// F68. The inductive ownership predicate takes its type parameter *implicitly*.
// ===========================================================================

/// This is the fact the probe exists for.
///
/// A C# method's type parameter is explicit (R14.2) because Roslyn resolved it and the
/// emitter should not ask F* to rediscover the answer. A *class*'s type parameter is in a
/// different position: every one of these definitions has a value argument whose type
/// already mentions it — `x: class_Node__opt a` — so `a` is determined, syntactically, by
/// unification with an argument the emitter is writing down anyway.
///
/// Making it implicit is therefore not a hope that inference will work out. It is the
/// observation that the emitter would otherwise be writing the same information twice. And
/// it has a concrete payoff: every *call site* of every lemma below is emitted by §10's
/// client rules and stays character for character what it already is.
let rec class_Node__inv_opt (#a: Type0) ([@@@mkey] x: class_Node__opt a) (p: perm)
                            (m: class_Node__model a)
  : Tot slprop (decreases m)
  = match m with
    | Nil -> pure (x == None)
    | Cons m0 m1 ->
      exists* (v: class_Node a) (r: class_Node__raw a).
        pure (x == Some v) **
        B.pts_to v #p r **
        pure (m0 == r.fld_value) **
        class_Node__inv_opt r.fld_next p m1

let class_Node__inv (#a: Type0) (this: class_Node a) (#[T.exact (`1.0R)] p: perm)
                    (m: class_Node__model a) : slprop =
  class_Node__inv_opt (Some this) p m

// ===========================================================================
// F69. Every case lemma R10.4 emits carries over unchanged but for the binder.
// ===========================================================================

ghost fn class_Node__cases (#a: Type0) (x: class_Node__opt a) (#p: perm)
                           (#m: class_Node__model a)
  preserves class_Node__inv_opt x p m
  ensures pure (Some? x <==> Cons? m)
{
  match m {
    Nil -> {
      unfold (class_Node__inv_opt x p Nil);
      fold (class_Node__inv_opt x p Nil);
    }
    Cons m0 m1 -> {
      unfold (class_Node__inv_opt x p (Cons m0 m1));
      with v r. assert (B.pts_to v #p r);
      fold (class_Node__inv_opt x p (Cons m0 m1));
    }
  }
}

ghost fn class_Node__nil_case (#a: Type0) (x: class_Node__opt a) (#p: perm)
                              (#m: class_Node__model a)
  preserves class_Node__inv_opt x p m
  requires pure (x == None)
  ensures pure (m == Nil)
{
  match m {
    Nil -> { () }
    Cons m0 m1 -> {
      unfold (class_Node__inv_opt x p (Cons m0 m1));
      with v r. assert (B.pts_to v #p r);
      unreachable ()
    }
  }
}

ghost fn class_Node__elim_nil (#a: Type0) (x: class_Node__opt a) (#p: perm)
                              (#m: class_Node__model a)
  requires class_Node__inv_opt x p m ** pure (x == None)
  ensures pure (m == Nil)
{
  class_Node__nil_case x;
  unfold (class_Node__inv_opt x p Nil);
}

ghost fn class_Node__intro_nil (#a: Type0) (x: class_Node__opt a) (p: perm)
  requires pure (x == None)
  ensures class_Node__inv_opt x p Nil
{
  fold (class_Node__inv_opt x p Nil)
}

ghost fn class_Node__elim_cons (#a: Type0) (x: class_Node__opt a { Some? x }) (#p: perm)
                               (#m: class_Node__model a)
  requires class_Node__inv_opt x p m
  ensures exists* (r: class_Node__raw a) (m1: class_Node__model a).
    B.pts_to (Some?.v x) #p r **
    class_Node__inv_opt r.fld_next p m1 **
    pure (m == Cons r.fld_value m1)
{
  match m {
    Nil -> {
      unfold (class_Node__inv_opt x p Nil);
      unreachable ()
    }
    Cons m0 m1 -> {
      unfold (class_Node__inv_opt x p (Cons m0 m1));
      with v r. assert (B.pts_to v #p r);
      rewrite each v as (Some?.v x);
      ()
    }
  }
}

ghost fn class_Node__intro_cons (#a: Type0) (x: class_Node__opt a { Some? x })
    (#p: perm) (#r: class_Node__raw a) (#m1: class_Node__model a)
  requires B.pts_to (Some?.v x) #p r **
           class_Node__inv_opt r.fld_next p m1
  ensures class_Node__inv_opt x p (Cons r.fld_value m1)
{
  fold (class_Node__inv_opt (Some (Some?.v x)) p (Cons r.fld_value m1));
  rewrite (class_Node__inv_opt (Some (Some?.v x)) p (Cons r.fld_value m1))
       as (class_Node__inv_opt x p (Cons r.fld_value m1));
}

ghost fn class_Node__intro (#a: Type0) (this: class_Node a)
    (#p: perm) (#r: class_Node__raw a) (#m1: class_Node__model a)
  requires B.pts_to this #p r **
           class_Node__inv_opt r.fld_next p m1
  ensures class_Node__inv this #p (Cons r.fld_value m1)
{
  rewrite (B.pts_to this #p r) as (B.pts_to (Some?.v (Some this)) #p r);
  class_Node__intro_cons (Some this);
  rewrite (class_Node__inv_opt (Some this) p (Cons r.fld_value m1))
       as (class_Node__inv this #p (Cons r.fld_value m1));
}

ghost fn class_Node__as_opt (#a: Type0) (this: class_Node a) (#p: perm)
                            (#m: class_Node__model a)
  requires class_Node__inv this #p m
  ensures class_Node__inv_opt (Some this) p m
{
  rewrite (class_Node__inv this #p m) as (class_Node__inv_opt (Some this) p m);
}

// ===========================================================================
// F70. Recursive share and gather carry over, including their `decreases`.
// ===========================================================================

ghost fn rec class_Node__inv_opt_share (#a: Type0) (x: class_Node__opt a) (#p: perm)
                                       (#m: class_Node__model a)
  requires class_Node__inv_opt x p m
  ensures class_Node__inv_opt x (p /. 2.0R) m ** class_Node__inv_opt x (p /. 2.0R) m
  decreases m
{
  class_Node__cases x;
  if (None? x) {
    class_Node__elim_nil x;
    class_Node__intro_nil x (p /. 2.0R);
    class_Node__intro_nil x (p /. 2.0R);
  } else {
    class_Node__elim_cons x;
    with r m1. assert (B.pts_to (Some?.v x) #p r ** class_Node__inv_opt r.fld_next p m1);
    B.share (Some?.v x);
    class_Node__inv_opt_share r.fld_next #p #m1;
    class_Node__intro_cons x #(p /. 2.0R) #r #m1;
    class_Node__intro_cons x #(p /. 2.0R) #r #m1;
  }
}

[@@allow_ambiguous]
ghost fn rec class_Node__inv_opt_gather (#a: Type0) (x: class_Node__opt a) (p q: perm)
    (#m #alt_m: class_Node__model a)
  requires class_Node__inv_opt x p m ** class_Node__inv_opt x q alt_m
  ensures class_Node__inv_opt x (p +. q) m ** pure (m == alt_m)
  decreases m
{
  class_Node__cases x #p #m;
  class_Node__cases x #q #alt_m;
  if (None? x) {
    class_Node__elim_nil x #p #m;
    class_Node__elim_nil x #q #alt_m;
    class_Node__intro_nil x (p +. q);
  } else {
    class_Node__elim_cons x #p #m;
    with r m1. assert (B.pts_to (Some?.v x) #p r ** class_Node__inv_opt r.fld_next p m1);
    class_Node__elim_cons x #q #alt_m;
    with alt_r alt_m1. assert (B.pts_to (Some?.v x) #q alt_r ** class_Node__inv_opt alt_r.fld_next q alt_m1);
    B.gather (Some?.v x);
    rewrite each alt_r as r;
    class_Node__inv_opt_gather r.fld_next p q #m1 #alt_m1;
    class_Node__intro_cons x #(p +. q) #r #m1;
  }
}

// ===========================================================================
// F71. A generic method over a generic class needs no new rule.
// ===========================================================================

/// This is the M8 shape (an explicit `ty_T` binder, R14.2) meeting the M9 shape (a class
/// applied to it). The traversal is the emitted `Func_Lists_Length` with `class_Node__opt`
/// applied to the method's own type variable.
///
/// Every lemma call below is *unchanged* from the monomorphic emission — no `#ty_T`, no
/// `ty_T` — which is F68's payoff, and the reason the client half of §15 is so much
/// smaller than it might have been.
///
/// The control immediately below is the same body at a fixed element type. It is here
/// because the first draft of the generic one failed, and the control is what proved the
/// failure had nothing to do with generics: written with `preserves` and an unerased
/// model, *both* forms fail, and written in the emitter's own idiom — an `erased` model,
/// `requires`/`ensures` spelled out — both succeed. The rule that survives is R10.7's,
/// unchanged; the lesson is that a probe has to be written in the emitter's idiom or it
/// measures the probe.
// --- control: the same body at a fixed element type, in the emitter's own idiom ---
fn rec ctrl_Length (var_n: class_Node__opt I32.t)
                   (#pre_n: erased (class_Node__model I32.t)) (#p: perm)
  requires class_Node__inv_opt var_n p pre_n **
           pure ((L.length (reveal pre_n)) < 2147483647)
  returns  var_result: I32.t
  ensures  class_Node__inv_opt var_n p pre_n **
           pure ((I32.v var_result) == (L.length (reveal pre_n)))
  decreases (reveal pre_n)
{
  class_Node__cases var_n;
  if (None? var_n) {
    class_Node__nil_case var_n;
    0l
  } else {
    class_Node__elim_cons var_n;
    let t1 = B.op_Bang (Some?.v var_n);
    let t0 = ctrl_Length t1.fld_next;
    let t2 = (I32.add 1l t0);
    class_Node__intro_cons var_n;
    t2
  }
}

fn rec func_Lists_Length (ty_T: Type0) (var_n: class_Node__opt ty_T)
                         (#pre_n: erased (class_Node__model ty_T)) (#p: perm)
  requires class_Node__inv_opt var_n p pre_n **
           pure ((L.length (reveal pre_n)) < 2147483647)
  returns  var_result: I32.t
  ensures  class_Node__inv_opt var_n p pre_n **
           pure ((I32.v var_result) == (L.length (reveal pre_n)))
  decreases (reveal pre_n)
{
  class_Node__cases var_n;
  if (None? var_n) {
    class_Node__nil_case var_n;
    0l
  } else {
    class_Node__elim_cons var_n;
    let t1 = B.op_Bang (Some?.v var_n);
    let t0 = func_Lists_Length ty_T t1.fld_next;
    let t2 = (I32.add 1l t0);
    class_Node__intro_cons var_n;
    t2
  }
}

// ===========================================================================
// F72. A generic *handle* class owning a generic recursive one.
// ===========================================================================

/// R3.10b over a generic field: `LinkedList<T>` is not itself recursive, but it owns a
/// `Node<T>?`. The sub-invariant is the inductive one at the *same* type argument, which
/// is the only thing the owner has to say about it.
noeq type class_LinkedList__raw (a: Type0) = {
  fld_head: class_Node__opt a;
}

type class_LinkedList (a: Type0) = B.box (class_LinkedList__raw a)

let class_LinkedList__inv (#a: Type0) (this: class_LinkedList a)
                          (#[T.exact (`1.0R)] p: perm) (m: list a) : slprop =
  exists* (r: class_LinkedList__raw a) (model_head: class_Node__model a).
    B.pts_to this #p r **
    class_Node__inv_opt r.fld_head p model_head **
    pure (m == model_head)

ghost fn class_LinkedList__unfold (#a: Type0) (this: class_LinkedList a) (#p: perm)
                                  (#m: list a)
  requires class_LinkedList__inv this #p m
  ensures exists* (r: class_LinkedList__raw a) (model_head: class_Node__model a).
    B.pts_to this #p r **
    class_Node__inv_opt r.fld_head p model_head **
    pure (m == model_head)
{
  unfold (class_LinkedList__inv this #p m);
}
