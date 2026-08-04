module UserSpecFacts

/// Pinned facts for **user-defined specification types** (doc/translation.md §11).
///
/// Like the other files in `test/pulse_facts`, this is NOT a translation target and NOT a
/// golden file. It is the §0 probe: every shape §11 is specified to produce is written
/// here by hand *first*, in the emitter's own idiom, and verified.
///
/// The question §11 asks is whether §10's machinery is tied to `list` and to
/// `Pulse.Lib.CSharp.Tree.tree` — the two model types the compiler currently knows by
/// name — or whether it only ever needed *a* type with a nullary constructor and a
/// recursive one. If the latter, the compiler can stop knowing any of them by name, and a
/// user can bring their own.
///
/// Three things have to hold for that to work, and each is a numbered section below.
///
///   1. The constructors of `list` are ordinary prefix constructors, so a scheme written
///      in terms of "the empty constructor" and "the non-empty constructor" covers `list`
///      too, and there is no need for a special case for `[]` and `::`.
///   2. An inductive declared *outside* the compiler — in a module the user supplied — is
///      usable as a class's model with no property `list` has that it lacks.
///   3. The constructor's *arity* is not fixed at two or three. A shape with two pure
///      arguments and one recursive one, which is neither a list nor a tree, works
///      through the same rules.

open Pulse

module B = Pulse.Lib.Box
open Pulse.Lib.Box { box, (!), (:=) }
module I32 = FStar.Int32
module L = FStar.List.Tot
module T = FStar.Tactics

#lang-pulse

// ===========================================================================
// 1. F*'s `list` has ordinary constructors (F46)
// ===========================================================================

/// F46. `[]` and `::` are *notation* for `Nil` and `Cons`, which are ordinary prefix
/// constructors of an ordinary inductive, and `Cons?` is the ordinary discriminator.
///
/// This is the fact that lets §11 delete the last special case. §10's emitter renders the
/// empty model as the literal text `[]` and the non-empty one as the infix `hd :: tl`,
/// with a `RecursiveShape` enum in the compiler choosing between that and the tree's
/// prefix form. If `Nil` and `Cons` work in every position `[]` and `::` do — as a term,
/// as a *pattern*, and under a discriminator — then the emitter needs only a constructor
/// *name* and an arity, both of which a user can declare.
let nil_is_prefix (#a: Type0) () : Lemma (Nil #a == ([] <: list a)) = ()

let cons_is_prefix (#a: Type0) (hd: a) (tl: list a)
  : Lemma (Cons hd tl == hd :: tl)
  = ()

/// As a pattern, and with the discriminator. Both arms are written the prefix way.
let rec length_prefix (#a: Type0) (l: list a) : Tot nat (decreases l) =
  match l with
  | Nil -> 0
  | Cons _ tl -> 1 + length_prefix tl

let cons_test (#a: Type0) (l: list a)
  : Lemma (Cons? l <==> (match l with | [] -> False | _ -> True))
  = ()

// ===========================================================================
// 2. A user-declared inductive, with a constructor arity neither list nor tree has
// ===========================================================================

/// This stands for the F* module a user supplies through `[assembly: IncludePulse]`, or
/// any module already on the include path. Nothing about it is known to the compiler: §11
/// learns its name, its constructors and their arities from *attributes in the C# file*,
/// and emits exactly what it is told.
///
/// The shape is deliberately not a list and not a tree: `Entry` carries **two** pure
/// arguments — a key and a value — and **one** recursive argument. §10's `RecursiveShape`
/// enum cannot name it, which is the point.
noeq type assoc (k: Type0) (v: Type0) =
  | Empty : assoc k v
  | Entry : k -> v -> assoc k v -> assoc k v

let rec assoc_length (#k #v: Type0) (m: assoc k v) : Tot nat (decreases m) =
  match m with
  | Empty -> 0
  | Entry _ _ tl -> 1 + assoc_length tl

let rec assoc_find (#v: Type0) (m: assoc int v) (key: int) : Tot (option v) (decreases m) =
  match m with
  | Empty -> None
  | Entry k x tl -> if k = key then Some x else assoc_find tl key

// ===========================================================================
// 3. The §10 encoding, over that type, unchanged (F47)
// ===========================================================================

/// The C# this stands for is
///
///   [SpecType("UserSpecFacts.assoc")] ... // declared in the user's own file
///
///   public sealed class Pair {
///       internal int key; internal int val; internal Pair? next;
///       [Model] private SpecAssoc Entries => SpecAssoc.Entry(key, val, next!.Entries);
///   }
///
/// R10.1's mutually recursive group, unchanged.
noeq type class_Pair__raw = {
  fld_key: I32.t;
  fld_val: I32.t;
  fld_next: class_Pair__opt;
}
and class_Pair = B.box class_Pair__raw
and class_Pair__opt = option class_Pair

type class_Pair__model = assoc int int

/// F47. R10.3's inductive invariant, at the new shape. The only differences from
/// `RecursiveFacts.class_Node__inv_opt` are the constructor's *name* and the *number* of
/// `pure` equations in the non-empty case — one per pure argument. Both are read off the
/// user's `[SpecCtor]` declaration, so the emitter's template is unchanged.
let rec class_Pair__inv_opt ([@@@mkey] x: class_Pair__opt) (p: perm) (m: class_Pair__model)
  : Tot slprop (decreases m)
  = match m with
    | Empty -> pure (x == None)
    | Entry k0 v1 tl ->
      exists* (o: class_Pair) (r: class_Pair__raw).
        pure (x == Some o) **
        B.pts_to o #p r **
        pure (k0 == I32.v r.fld_key) **
        pure (v1 == I32.v r.fld_val) **
        class_Pair__inv_opt r.fld_next p tl

let class_Pair__inv (this: class_Pair) (#[T.exact (`1.0R)] p: perm) (m: class_Pair__model)
  : slprop
  = class_Pair__inv_opt (Some this) p m

// ===========================================================================
// 4. The derived lemmas (R10.4), at the new shape
// ===========================================================================

ghost fn class_Pair__cases (x: class_Pair__opt) (#p: perm) (#m: class_Pair__model)
  preserves class_Pair__inv_opt x p m
  ensures pure (Some? x <==> Entry? m)
{
  match m {
    Empty -> {
      unfold (class_Pair__inv_opt x p Empty);
      fold (class_Pair__inv_opt x p Empty);
    }
    Entry k0 v1 tl -> {
      unfold (class_Pair__inv_opt x p (Entry k0 v1 tl));
      with o r. assert (B.pts_to o #p r);
      fold (class_Pair__inv_opt x p (Entry k0 v1 tl));
    }
  }
}

ghost fn class_Pair__nil_case (x: class_Pair__opt) (#p: perm) (#m: class_Pair__model)
  preserves class_Pair__inv_opt x p m
  requires pure (x == None)
  ensures pure (m == Empty)
{
  match m {
    Empty -> { () }
    Entry k0 v1 tl -> {
      unfold (class_Pair__inv_opt x p (Entry k0 v1 tl));
      with o r. assert (B.pts_to o #p r);
      unreachable ()
    }
  }
}

ghost fn class_Pair__elim_nil (x: class_Pair__opt) (#p: perm) (#m: class_Pair__model)
  requires class_Pair__inv_opt x p m ** pure (x == None)
  ensures pure (m == Empty)
{
  class_Pair__nil_case x;
  unfold (class_Pair__inv_opt x p Empty);
}

ghost fn class_Pair__intro_nil (x: class_Pair__opt) (p: perm)
  requires pure (x == None)
  ensures class_Pair__inv_opt x p Empty
{
  fold (class_Pair__inv_opt x p Empty)
}

/// The existential names one binder per *recursive* argument and reports the model as the
/// constructor applied to the pure fields and those binders — the same template as §10's,
/// with three arguments instead of two.
ghost fn class_Pair__elim_cons (x: class_Pair__opt { Some? x }) (#p: perm) (#m: class_Pair__model)
  requires class_Pair__inv_opt x p m
  ensures exists* (r: class_Pair__raw) (tl: class_Pair__model).
    B.pts_to (Some?.v x) #p r **
    class_Pair__inv_opt r.fld_next p tl **
    pure (m == Entry (I32.v r.fld_key) (I32.v r.fld_val) tl)
{
  match m {
    Empty -> {
      unfold (class_Pair__inv_opt x p Empty);
      unreachable ()
    }
    Entry k0 v1 tl -> {
      unfold (class_Pair__inv_opt x p (Entry k0 v1 tl));
      with o r. assert (B.pts_to o #p r);
      rewrite (B.pts_to o #p r) as (B.pts_to (Some?.v x) #p r);
      rewrite (class_Pair__inv_opt r.fld_next p tl)
           as (class_Pair__inv_opt r.fld_next p tl);
    }
  }
}

ghost fn class_Pair__intro_cons (x: class_Pair__opt { Some? x })
    (#p: perm) (#r: class_Pair__raw) (#tl: class_Pair__model)
  requires B.pts_to (Some?.v x) #p r ** class_Pair__inv_opt r.fld_next p tl
  ensures class_Pair__inv_opt x p (Entry (I32.v r.fld_key) (I32.v r.fld_val) tl)
{
  fold (class_Pair__inv_opt (Some (Some?.v x)) p
         (Entry (I32.v r.fld_key) (I32.v r.fld_val) tl));
  rewrite (class_Pair__inv_opt (Some (Some?.v x)) p
            (Entry (I32.v r.fld_key) (I32.v r.fld_val) tl))
       as (class_Pair__inv_opt x p (Entry (I32.v r.fld_key) (I32.v r.fld_val) tl));
}

// ===========================================================================
// 5. A traversal (R10.7), to show the window rule is shape-independent
// ===========================================================================

/// The C# this stands for is
///
///   [Requires("...")] [Ensures("Result == p.Entries.Length")] [Decreases("p.Entries")]
///   public static int Count(Pair? p) { if (p == null) { return 0; } return 1 + Count(p.next); }
///
/// Every proof step is the one §10 already places; nothing here mentions `list`.
fn rec func_Pairs_Count (var_p: class_Pair__opt) (#pre_p: erased class_Pair__model)
  requires class_Pair__inv_opt var_p 1.0R pre_p ** pure (assoc_length pre_p < 2147483647)
  returns  var_result: I32.t
  ensures  class_Pair__inv_opt var_p 1.0R pre_p **
           pure (I32.v var_result == assoc_length pre_p)
  decreases (reveal pre_p)
{
  class_Pair__cases var_p;
  if (None? var_p) {
    class_Pair__nil_case var_p;
    0l
  } else {
    class_Pair__elim_cons var_p;
    let t1 = B.op_Bang (Some?.v var_p);
    let t0 = func_Pairs_Count t1.fld_next;
    let t2 = I32.add 1l t0;
    class_Pair__intro_cons var_p;
    t2
  }
}

// ===========================================================================
// 6. A destructive traversal (R10.6b), at the new shape
// ===========================================================================

let rec assoc_set (m: assoc int int) (key: int) (x: int) : Tot (assoc int int) (decreases m) =
  match m with
  | Empty -> Empty
  | Entry k v tl -> if k = key then Entry k x tl else Entry k v (assoc_set tl key x)

/// The C# this stands for is
///
///   [Ensures("...")] [Decreases("p.Entries")]
///   public static void Set(Pair? p, int key, int x) {
///       if (p != null) { if (p.key == key) { p.val = x; } else { Set(p.next, key, x); } }
///   }
///
/// A field *write* inside the window, which is what makes this the interesting case: the
/// closing `intro_cons` re-establishes the invariant at the model the write produced,
/// which for a two-pure-argument constructor means the second `pure` equation is the one
/// that changed.
fn rec func_Pairs_Set (var_p: class_Pair__opt) (var_key: I32.t) (var_x: I32.t)
                      (#pre_p: erased class_Pair__model)
  requires class_Pair__inv_opt var_p 1.0R pre_p
  ensures  class_Pair__inv_opt var_p 1.0R
             (assoc_set pre_p (I32.v var_key) (I32.v var_x))
  decreases (reveal pre_p)
{
  class_Pair__cases var_p;
  if (None? var_p) {
    class_Pair__nil_case var_p;
    ()
  } else {
    class_Pair__elim_cons var_p;
    let t0 = B.op_Bang (Some?.v var_p);
    if (I32.eq t0.fld_key var_key) {
      B.op_Colon_Equals (Some?.v var_p) { t0 with fld_val = var_x };
      class_Pair__intro_cons var_p;
      ()
    } else {
      func_Pairs_Set t0.fld_next var_key var_x;
      class_Pair__intro_cons var_p;
      ()
    }
  }
}
