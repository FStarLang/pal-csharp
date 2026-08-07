module CursorFacts
#lang-pulse

/// §0 probe for §16: *cursors*, i.e. iterative traversal of a linked structure.
///
/// This is the shape §10.7 recorded as out of reach and §15.5 repeated. A recursive class's
/// derived invariant `class_C__inv_opt x p m` owns the list *from `x` to the end*, so a loop
/// that advances a cursor through it has nowhere to put the part it has already walked.
/// R10.7 opens a window at a null test and closes it at the end of the branch, which is
/// exactly a recursive traversal and exactly not an iterative one.
///
/// §12 is the answer and this file is its probe. What a cursor needs is a *list segment* --
/// bounded at both ends, so that the prefix already walked is one instance of the predicate
/// and the suffix still to walk is another -- and §12's `[Plain]` is how a user gets to
/// state one. Three things are new here relative to `SegmentFacts`:
///
///   1. the predicate is **generic** (§15), so it is stated at `a: Type0` and the C# class
///      it is about is a generic `[Plain]` class;
///   2. the split point is a **mutable** cursor, so the loop invariant has to be able to say
///      where the split currently is;
///   3. the interesting lemma is `advance`, which moves the split point one cell to the
///      right -- the `snoc` §12.4 named as the step an iterative traversal takes.
///
/// The design decision this file exists to pin is (2), and it is what makes the whole thing
/// land inside the *existing* loop rule. A pal-csharp loop invariant existentially
/// quantifies the mutable locals and nothing else (R5.8), so a segment whose contents were
/// an arbitrary existential list could not be stated at all. It does not have to be: the
/// prefix is `take l i` and the suffix is `drop l i`, both **functions of the loop counter**,
/// which is a mutable local and so is quantified already. That is not a contrivance to fit
/// the rule -- it is the invariant a person writes by hand -- but it does mean §16 needs no
/// new loop machinery beyond letting an invariant clause be an `slprop` at all.
///
/// `take` and `drop` are `Pulse.Lib.CSharp.List`'s, not hand-rolled ones, because they are
/// what the emitter already produces for a C# `xs.Take(i)` (R15.7). Pinning the design
/// against the *clamped, unrefined* pair is the whole point: a cursor that needed a refined
/// `n: nat{n <= length l}` could not be spelled in a C# specification at all. For the same
/// reason every index below is an `int` with `0 <= i` in the `pure` part rather than a
/// `nat`: a C# `int` reaches a specification as a mathematical integer and nothing more.

open Pulse
module B = Pulse.Lib.Box
module R = Pulse.Lib.Reference
module I32 = FStar.Int32
module L = FStar.List.Tot
module CL = Pulse.Lib.CSharp.List

// ===========================================================================
// 1. The representation: a generic `[Plain]` class, exactly as R12.1 + R15.1 emit it
// ===========================================================================

///   [Plain]
///   public sealed class Cell<T>
///   {
///       internal T value;
///       internal Cell<T>? next;
///   }
///
/// R15.1 makes the record a function of the type parameter; R12.1 stops there. No
/// `__inv_opt`, no derived lemmas, no ownership of any kind attached to the type.
noeq type class_Cell__raw (ty_T: Type0) = {
  fld_value: ty_T;
  fld_next: (class_Cell__opt ty_T);
}
and class_Cell (ty_T: Type0) = B.box (class_Cell__raw ty_T)
and class_Cell__opt (ty_T: Type0) = option (class_Cell ty_T)

// ===========================================================================
// 2. The arithmetic of a split point
// ===========================================================================

/// The three facts about `take`/`drop` a cursor needs and the library's SMT patterns do not
/// already give. All three are about *stepping* the split point, which is the one thing a
/// recursive traversal never does -- so it is unsurprising that they were not needed before.

/// Advancing past element `i` takes one element off the front of the suffix.
let rec drop_step (#a: Type) (l: list a) (i: int)
  : Lemma (requires 0 <= i /\ i < L.length l)
          (ensures  CL.drop l i == L.index l i :: CL.drop l (i + 1))
          (decreases l)
  = if i = 0 then () else match l with _ :: tl -> drop_step tl (i - 1)

/// ... and puts that same element on the *end* of the prefix. This is `snoc` at the level
/// of the list; `seg_snoc` below is the same statement at the level of the heap.
let rec take_step (#a: Type) (l: list a) (i: int)
  : Lemma (requires 0 <= i /\ i < L.length l)
          (ensures  CL.take l (i + 1) == L.append (CL.take l i) [L.index l i])
          (decreases l)
  = if i = 0 then () else match l with _ :: tl -> take_step tl (i - 1)

/// When the cursor has arrived, the prefix is everything.
let rec take_all (#a: Type) (l: list a) (i: int)
  : Lemma (requires i >= L.length l) (ensures CL.take l i == l) (decreases l)
  = if i <= 0 then () else match l with [] -> () | _ :: tl -> take_all tl (i - 1)

/// The suffix is non-empty exactly while there is something left to walk. This is the
/// arithmetic half of a cursor's loop condition; `seg_at_end` below is the half that ties it
/// to the pointer.
let drop_cons_iff (#a: Type) (l: list a) (i: int)
  : Lemma (requires 0 <= i /\ i <= L.length l)
          (ensures  Cons? (CL.drop l i) <==> i < L.length l)
  = CL.drop_length l i;
    if i < L.length l then drop_step l i else ()

// ===========================================================================
// 3. The predicate: a segment, at a type parameter
// ===========================================================================

/// `cell_seg p from to_ l` owns the cells from `from` up to but not including `to_`,
/// holding `l`.
///
/// `[@@@mkey]` on `from` is the annotation the emitter puts on a derived invariant's
/// reference: it tells Pulse's matcher which argument identifies the instance, so that the
/// two segments a cursor holds at once are told apart by where they start.
///
/// Note the nil case: `from == to_`, a relation between *two* parameters. That is the
/// clause a derived invariant can never have, and the reason a cursor needs §12.
let rec cell_seg (#a: Type0) (p: perm)
                 ([@@@mkey] from: class_Cell__opt a) (to_: class_Cell__opt a)
                 (l: list a)
  : Tot slprop (decreases l)
  = match l with
    | [] -> pure (from == to_)
    | hd :: tl ->
      exists* (v: class_Cell a) (r: class_Cell__raw a).
        pure (from == Some v) **
        B.pts_to v #p r **
        pure (hd == r.fld_value) **
        cell_seg p r.fld_next to_ tl

/// The friendly names a C# `[SpecOp]` maps onto. Both are `unfold`, so Pulse's (syntactic)
/// resource matching still sees `cell_seg` and every lemma below applies through them.
unfold
let seg (#a: Type0) (from to_: class_Cell__opt a) (l: list a) : slprop =
  cell_seg 1.0R from to_ l

/// A whole chain is the segment that ends at `null`. Saying it this way rather than as a
/// second recursive predicate is what lets a cursor's prefix and its suffix be *the same*
/// predicate, which is what makes `advance` a statement about one thing rather than two.
unfold
let whole (#a: Type0) (from: class_Cell__opt a) (l: list a) : slprop =
  cell_seg 1.0R from None l

// ===========================================================================
// 4. The structural lemmas
// ===========================================================================

/// The empty segment costs nothing.
ghost fn seg_nil (#a: Type0) (x: class_Cell__opt a)
  requires emp
  ensures  cell_seg 1.0R x x ([] <: list a)
{
  fold (cell_seg 1.0R x x ([] <: list a));
}

/// The null test is a statement about the *list*, and for a segment it is valid only when
/// the right boundary is `None`. §12 refuses to derive it and makes the user state it;
/// stated once here, every loop that tests its cursor against null gets it by calling.
ghost fn seg_cases (#a: Type0) (from: class_Cell__opt a) (l: list a)
  preserves whole from l
  ensures  pure (Some? from <==> Cons? l)
{
  match l {
    Nil -> {
      unfold (cell_seg 1.0R from None ([] <: list a));
      fold (cell_seg 1.0R from None ([] <: list a));
    }
    Cons hd tl -> {
      unfold (cell_seg 1.0R from None (hd :: tl));
      with v r. assert (B.pts_to v r);
      fold (cell_seg 1.0R from None (hd :: tl));
    }
  }
}

/// Introducing a cons cell on the left. The cell's two field values are named rather than
/// projected out of an existential record, which is what lets a C# caller -- who has just
/// *read* those two fields -- name them too.
ghost fn seg_intro_cons (#a: Type0)
    (v: class_Cell a) (value: a) (next to_: class_Cell__opt a) (tl: list a)
  requires B.pts_to v ({ fld_value = value; fld_next = next }) **
           cell_seg 1.0R next to_ tl
  ensures  cell_seg 1.0R (Some v) to_ (value :: tl)
{
  fold (cell_seg 1.0R (Some v) to_ (value :: tl));
}

/// Two adjacent segments compose. §12.4 called this "the lemma no `[Model]` could produce",
/// and it is the only induction in the file.
///
/// It is also the reason a cursor is a §12 problem rather than a §10 one: it relates *two*
/// instances of the predicate, which is precisely what reading a `[Model]` backwards cannot
/// give you. Everything else below is this lemma with the boundaries arranged differently.
ghost fn rec seg_append (#a: Type0)
    (head from to_: class_Cell__opt a) (l1 l2: list a)
  requires cell_seg 1.0R head from l1 ** cell_seg 1.0R from to_ l2
  ensures  cell_seg 1.0R head to_ (L.append l1 l2)
  decreases l1
{
  match l1 {
    Nil -> {
      unfold (cell_seg 1.0R head from ([] <: list a));
      rewrite (cell_seg 1.0R from to_ l2)
           as (cell_seg 1.0R head to_ (L.append ([] <: list a) l2));
    }
    Cons hd tl -> {
      unfold (cell_seg 1.0R head from (hd :: tl));
      with w r. assert (B.pts_to w #1.0R r);
      seg_append r.fld_next from to_ tl l2;
      rewrite (B.pts_to w #1.0R r)
           as (B.pts_to w ({ fld_value = r.fld_value; fld_next = r.fld_next }));
      seg_intro_cons w r.fld_value r.fld_next to_ (L.append tl l2);
      rewrite (cell_seg 1.0R (Some w) to_ (r.fld_value :: L.append tl l2))
           as (cell_seg 1.0R head to_ (L.append (hd :: tl) l2));
    }
  }
}

/// Extending a segment on the **right**: the cell the segment currently stops at is
/// absorbed into it, and the segment now stops one cell further on.
///
/// This is the lemma §12.4 called `snoc` and named as the step an iterative traversal takes.
/// It is `seg_append` with a one-cell segment on the right, and writing it that way rather
/// than by its own induction is the point: the *step* of a loop is not a new idea, it is the
/// composition lemma at a particular pair of boundaries.
ghost fn seg_snoc (#a: Type0)
    (head from: class_Cell__opt a) (v: class_Cell a)
    (value: a) (next: class_Cell__opt a) (l: list a)
  requires cell_seg 1.0R head from l **
           B.pts_to v ({ fld_value = value; fld_next = next }) **
           pure (from == Some v)
  ensures  cell_seg 1.0R head next (L.append l [value])
{
  seg_nil next;
  seg_intro_cons v value next next ([] <: list a);
  rewrite (cell_seg 1.0R (Some v) next [value])
       as (cell_seg 1.0R from next [value]);
  seg_append head from next l [value];
}

// ===========================================================================
// 5. The C# face: one lemma per step a C# loop takes
// ===========================================================================

/// `opened from v value next to_ l` is `seg from to_ l` with its first cell unfolded.
///
/// It names four things the caller can also name: the nullable cursor `from` that the loop
/// invariant talks about, the box `v` a field access reads through, and the two field
/// *values* `value` and `next` the C# body is about to read out. `SegmentFacts` §6
/// established the first pair; the second pair is what an *iterative* step needs, because
/// the new split point is `next` -- a value that exists only once the heap has been read.
///
/// So `seg_open` produces it existentially and the C# body picks the witnesses up by reading
/// the fields; `seg_advance` takes them back as ordinary arguments.
unfold
let opened (#a: Type0) (from: class_Cell__opt a) (v: class_Cell a)
           (value: a) (next: class_Cell__opt a)
           (to_: class_Cell__opt a) (l: list a)
  : slprop
  = exists* (tl: list a).
      B.pts_to v ({ fld_value = value; fld_next = next }) **
      cell_seg 1.0R next to_ tl **
      pure (from == Some v /\ l == value :: tl)

/// The loop condition, stated once so that no C# body has to reason about it. `seg_cases`
/// ties the null test to the *shape* of the suffix; this ties it to the *counter*, which is
/// what a loop invariant indexed by `take`/`drop` actually needs.
ghost fn seg_at_end (#a: Type0) (from: class_Cell__opt a) (i: int) (l: list a)
  preserves seg from None (CL.drop l i)
  requires pure (0 <= i /\ i <= L.length l)
  ensures  pure ((None? from <==> i == L.length l) /\
                 (Some? from <==> Cons? (CL.drop l i)))
{
  drop_cons_iff l i;
  seg_cases from (CL.drop l i);
}

/// Start the walk. `take l 0` is `[]` and `drop l 0` is `l`, so the loop is entered with
/// `cur = head` and `i = 0` and the invariant holds by construction.
ghost fn seg_start (#a: Type0) (head: class_Cell__opt a) (l: list a)
  requires whole head l
  ensures  seg head head (CL.take l 0) ** seg head None (CL.drop l 0)
{
  seg_nil head;
  rewrite (cell_seg 1.0R head head ([] <: list a))
       as (cell_seg 1.0R head head (CL.take l 0));
  rewrite (cell_seg 1.0R head None l)
       as (cell_seg 1.0R head None (CL.drop l 0));
}

/// Open the first cell of a non-empty suffix. Every `rewrite` the elimination needs stays
/// inside; what comes out is `opened`, whose two field values the C# body then reads.
ghost fn seg_open (#a: Type0) (from: class_Cell__opt a) (v: class_Cell a) (l: list a)
  requires whole from l ** pure (Cons? l /\ from == Some v)
  ensures  exists* (value: a) (next: class_Cell__opt a). opened from v value next None l
{
  rewrite (cell_seg 1.0R from None l) as (cell_seg 1.0R from None (L.hd l :: L.tl l));
  unfold (cell_seg 1.0R from None (L.hd l :: L.tl l));
  with w r. assert (B.pts_to w #1.0R r);
  rewrite each w as v;
  rewrite (B.pts_to v #1.0R r)
       as (B.pts_to v ({ fld_value = r.fld_value; fld_next = r.fld_next }));
  fold (opened from v r.fld_value r.fld_next None l);
}

/// The step. `seg_advance` moves the split point one cell to the right: the cell just
/// opened is appended to the prefix and taken off the front of the suffix, which is `snoc`
/// on one and `tl` on the other, at once.
///
/// Both halves are `take`/`drop` of the counter, so the caller never has to name the prefix
/// or the suffix -- it names `i`, and the predicate says the rest. The `ensures` also
/// reports what was read, which is how a C# body learns that the value it just took out of
/// the cell is element `i` of the list it was given.
ghost fn seg_advance (#a: Type0)
    (head from: class_Cell__opt a) (v: class_Cell a)
    (value: a) (next: class_Cell__opt a) (i: int) (l: list a)
  requires seg head from (CL.take l i) **
           opened from v value next None (CL.drop l i) **
           pure (0 <= i /\ i < L.length l)
  ensures  seg head next (CL.take l (i + 1)) **
           seg next None (CL.drop l (i + 1)) **
           pure ((0 <= i /\ i < L.length l) ==> value == L.index l i)
{
  drop_step l i;
  take_step l i;
  unfold (opened from v value next None (CL.drop l i));
  with tl. assert (cell_seg 1.0R next None tl);
  rewrite (cell_seg 1.0R next None tl)
       as (cell_seg 1.0R next None (CL.drop l (i + 1)));
  seg_snoc head from v value next (CL.take l i);
  rewrite (cell_seg 1.0R head next (L.append (CL.take l i) [value]))
       as (cell_seg 1.0R head next (CL.take l (i + 1)));
}

/// Give the list back, from wherever the cursor happens to be. `seg_append` plus the
/// library's `take_drop`, and nothing else.
///
/// This is the step a C# body takes when it leaves the loop *early* -- a `return` from
/// inside the walk -- and the reason the cursor pays no penalty for doing so: the two halves
/// compose at any split point, not only at the end.
ghost fn seg_close (#a: Type0)
    (head from: class_Cell__opt a) (i: int) (l: list a)
  requires seg head from (CL.take l i) ** seg from None (CL.drop l i)
  ensures  whole head l
{
  seg_append head from None (CL.take l i) (CL.drop l i);
  CL.take_drop l i;
  rewrite (cell_seg 1.0R head None (L.append (CL.take l i) (CL.drop l i)))
       as (cell_seg 1.0R head None l);
}

/// Reaching `null` ends the walk: the counter has arrived at the length, and the list comes
/// back whole.
ghost fn seg_finish (#a: Type0)
    (head from: class_Cell__opt a) (i: int) (l: list a)
  requires seg head from (CL.take l i) **
           seg from None (CL.drop l i) **
           pure (0 <= i /\ i <= L.length l /\ from == None)
  ensures  whole head l ** pure (i == L.length l)
{
  seg_at_end from i l;
  seg_close head from i l;
}

// ===========================================================================
// 6. The worked program: an iterative traversal, with no `rewrite` in the caller
// ===========================================================================

/// The length of a chain, computed by a **loop**. Compare `Chains.Size` in
/// `test/generic_list`, which is the same function written recursively because §10.7 left it
/// no choice.
///
/// Everything between `seg_start` and `seg_finish` is something a C# body can write: four
/// lemma calls, two field reads, two assignments to mutable locals, and an invariant whose
/// every conjunct is a `[SpecOp]` applied to names in scope. There is no `with` and no
/// `rewrite` anywhere in this function, which is the claim §16 has to make good on.
fn chain_count (#a: Type0) (head: class_Cell__opt a) (#l: erased (list a))
  requires whole head l ** pure (L.length l < pow2 31 - 1)
  returns  n: I32.t
  ensures  whole head l ** pure (I32.v n == L.length l)
{
  seg_start head l;
  let mut cur = head;
  let mut i = 0l;
  while (let c = !cur; Some? c)
  invariant exists* (c: class_Cell__opt a) (k: I32.t).
    R.pts_to cur c ** R.pts_to i k **
    cell_seg 1.0R head c (CL.take l (I32.v k)) **
    cell_seg 1.0R c None (CL.drop l (I32.v k)) **
    pure (0 <= I32.v k /\ I32.v k <= L.length l /\ L.length l < pow2 31 - 1)
  decreases (L.length l - I32.v !i)
  {
    let c = !cur;
    let k = !i;
    seg_at_end c (I32.v k) l;
    seg_open c (Some?.v c) (CL.drop l (I32.v k));
    let t = B.op_Bang (Some?.v c);
    seg_advance head c (Some?.v c) t.fld_value t.fld_next (I32.v k) l;
    cur := t.fld_next;
    i := I32.add k 1l;
  };
  let c = !cur;
  let k = !i;
  seg_finish head c (I32.v k) l;
  k
}

/// Element `n`, by walking to it. Compare `chain_count`: the loop is the same and only the
/// condition differs, which is the ordinary payoff of having stated the invariant in terms
/// of the counter.
///
/// The interesting line is the last `seg_close`. This walk stops in the *middle* of the
/// list, which is what a C# `return` from inside a loop does, and it costs one lemma call
/// rather than a special case: the two halves compose at any split point.
///
/// It also pins the *output* half of `seg_advance` -- that the value read out of a cell is
/// element `i` of the list the caller passed in -- which is what makes a cursor useful for
/// anything beyond counting.
fn chain_at (#a: Type0) (head: class_Cell__opt a) (n: I32.t) (#l: erased (list a))
  requires whole head l **
           pure (0 <= I32.v n /\ I32.v n < L.length l /\ L.length l < pow2 31 - 1)
  returns  r: a
  ensures  whole head l **
           pure ((0 <= I32.v n /\ I32.v n < L.length l) ==> r == L.index l (I32.v n))
{
  seg_start head l;
  let mut cur = head;
  let mut i = 0l;
  while (let k = !i; I32.lt k n)
  invariant exists* (c: class_Cell__opt a) (k: I32.t).
    R.pts_to cur c ** R.pts_to i k **
    cell_seg 1.0R head c (CL.take l (I32.v k)) **
    cell_seg 1.0R c None (CL.drop l (I32.v k)) **
    pure (0 <= I32.v k /\ I32.v k <= I32.v n /\
          I32.v n < L.length l /\ L.length l < pow2 31 - 1)
  decreases (I32.v n - I32.v !i)
  {
    let c = !cur;
    let k = !i;
    seg_at_end c (I32.v k) l;
    seg_open c (Some?.v c) (CL.drop l (I32.v k));
    let t = B.op_Bang (Some?.v c);
    seg_advance head c (Some?.v c) t.fld_value t.fld_next (I32.v k) l;
    cur := t.fld_next;
    i := I32.add k 1l;
  };
  let c = !cur;
  let k = !i;
  seg_at_end c (I32.v k) l;
  seg_open c (Some?.v c) (CL.drop l (I32.v k));
  let t = B.op_Bang (Some?.v c);
  seg_advance head c (Some?.v c) t.fld_value t.fld_next (I32.v k) l;
  seg_close head t.fld_next (I32.v k + 1) l;
  t.fld_value
}
