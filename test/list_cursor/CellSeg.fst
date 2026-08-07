module CellSeg
#lang-pulse

/// The user's ownership predicate for `test/list_cursor`: a **list segment** over the
/// `[Plain]` generic class `Cell<T>` declared in `Cell.cs`, together with the proof steps a
/// C# body takes when it walks one.
///
/// Why a segment. A derived `[Model]` invariant (§10) owns a chain *from a node to the end*,
/// so a loop that advances a cursor has nowhere to put the part it has already walked --
/// which is why §10.7 recorded iterative traversal as out of reach. A segment is bounded at
/// both ends: the prefix already walked is one instance of the predicate and the suffix
/// still to walk is another, and the loop invariant simply holds both.
///
/// Why the two halves are `take` and `drop` of the loop counter. A pal-csharp loop
/// invariant existentially quantifies the mutable locals and nothing else (R5.8), so the
/// contents of the two segments must be *functions of a mutable local*. They are: the
/// counter. That is also the invariant a person writes by hand, and it is `Pulse.Lib.CSharp
/// .List`'s clamped, unrefined `take`/`drop` throughout (R15.7) -- exactly what a C#
/// `SpecList.Take(xs, i)` emits -- because a cursor that needed a refined `n: nat{n <= len}`
/// could not be spelled in a C# specification at all.
///
/// Pinned first, and independently, by `test/pulse_facts/CursorFacts.fst`.

open Pulse
module B = Pulse.Lib.Box
module L = FStar.List.Tot
module CL = Pulse.Lib.CSharp.List

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
                 ([@@@mkey] from: Class_Cell.class_Cell__opt a) (to_: Class_Cell.class_Cell__opt a)
                 (l: list a)
  : Tot slprop (decreases l)
  = match l with
    | [] -> pure (from == to_)
    | hd :: tl ->
      exists* (r: Class_Cell.class_Cell__raw a).
        B.pts_to from #p r **
        pure (hd == r.Class_Cell.fld_value) **
        cell_seg p r.Class_Cell.fld_next to_ tl

/// The friendly names a C# `[SpecOp]` maps onto. Both are `unfold`, so Pulse's (syntactic)
/// resource matching still sees `cell_seg` and every lemma below applies through them.
unfold
let seg (#a: Type0) (from to_: Class_Cell.class_Cell__opt a) (l: list a) : slprop =
  cell_seg 1.0R from to_ l

/// A whole chain is the segment that ends at `null`. Saying it this way rather than as a
/// second recursive predicate is what lets a cursor's prefix and its suffix be *the same*
/// predicate, which is what makes `advance` a statement about one thing rather than two.
unfold
let whole (#a: Type0) (from: Class_Cell.class_Cell__opt a) (l: list a) : slprop =
  cell_seg 1.0R from B.null l

// ===========================================================================
// 4. The structural lemmas
// ===========================================================================

/// The empty segment costs nothing.
ghost fn seg_nil (#a: Type0) (x: Class_Cell.class_Cell__opt a)
  requires emp
  ensures  cell_seg 1.0R x x ([] <: list a)
{
  fold (cell_seg 1.0R x x ([] <: list a));
}

/// The null test is a statement about the *list*, and for a segment it is valid only when
/// the right boundary is `null`. §12 refuses to derive it and makes the user state it;
/// stated once here, every loop that tests its cursor against null gets it by calling.
ghost fn seg_cases (#a: Type0) (from: Class_Cell.class_Cell__opt a) (l: list a)
  preserves whole from l
  ensures  pure (not (B.is_null from) <==> Cons? l)
{
  match l {
    Nil -> {
      unfold (cell_seg 1.0R from B.null ([] <: list a));
      fold (cell_seg 1.0R from B.null ([] <: list a));
    }
    Cons hd tl -> {
      unfold (cell_seg 1.0R from B.null (hd :: tl));
      with r. assert (B.pts_to from r);
      B.pts_to_not_null from;
      fold (cell_seg 1.0R from B.null (hd :: tl));
    }
  }
}

/// Introducing a cons cell on the left. The cell's two field values are named rather than
/// projected out of an existential record, which is what lets a C# caller -- who has just
/// *read* those two fields -- name them too.
ghost fn seg_intro_cons (#a: Type0)
    (v: Class_Cell.class_Cell__opt a) (value: a) (next to_: Class_Cell.class_Cell__opt a) (tl: list a)
  requires B.pts_to v ({ Class_Cell.fld_value = value; Class_Cell.fld_next = next }) **
           cell_seg 1.0R next to_ tl
  ensures  cell_seg 1.0R v to_ (value :: tl)
{
  fold (cell_seg 1.0R v to_ (value :: tl));
}

/// Two adjacent segments compose. §12.4 called this "the lemma no `[Model]` could produce",
/// and it is the only induction in the file.
///
/// It is also the reason a cursor is a §12 problem rather than a §10 one: it relates *two*
/// instances of the predicate, which is precisely what reading a `[Model]` backwards cannot
/// give you. Everything else below is this lemma with the boundaries arranged differently.
ghost fn rec seg_append (#a: Type0)
    (head from to_: Class_Cell.class_Cell__opt a) (l1 l2: list a)
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
      with r. assert (B.pts_to head #1.0R r);
      seg_append r.Class_Cell.fld_next from to_ tl l2;
      rewrite (B.pts_to head #1.0R r)
           as (B.pts_to head ({ Class_Cell.fld_value = r.Class_Cell.fld_value; Class_Cell.fld_next = r.Class_Cell.fld_next }));
      seg_intro_cons head r.Class_Cell.fld_value r.Class_Cell.fld_next to_ (L.append tl l2);
      rewrite (cell_seg 1.0R head to_ (r.Class_Cell.fld_value :: L.append tl l2))
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
    (head from: Class_Cell.class_Cell__opt a)
    (value: a) (next: Class_Cell.class_Cell__opt a) (l: list a)
  requires cell_seg 1.0R head from l **
           B.pts_to from ({ Class_Cell.fld_value = value; Class_Cell.fld_next = next })
  ensures  cell_seg 1.0R head next (L.append l [value])
{
  seg_nil next;
  seg_intro_cons from value next next ([] <: list a);
  seg_append head from next l [value];
}

// ===========================================================================
// 5. The C# face: one lemma per step a C# loop takes
// ===========================================================================

/// `opened from v value next to_ l` is `seg from to_ l` with its first cell unfolded.
///
/// It names three things the caller can also name: the cursor `from` that the loop
/// invariant talks about -- which under R10.2 is also the reference a field access reads
/// through, so it is named once -- and the two field *values* `value` and `next` the C#
/// body is about to read out. That second pair is what an *iterative* step needs, because
/// the new split point is `next` -- a value that exists only once the heap has been read.
///
/// So `seg_open` produces it existentially and the C# body picks the witnesses up by reading
/// the fields; `seg_advance` takes them back as ordinary arguments.
unfold
let opened (#a: Type0) (from: Class_Cell.class_Cell__opt a)
           (value: a) (next: Class_Cell.class_Cell__opt a)
           (to_: Class_Cell.class_Cell__opt a) (l: list a)
  : slprop
  = exists* (tl: list a).
      B.pts_to from ({ Class_Cell.fld_value = value; Class_Cell.fld_next = next }) **
      cell_seg 1.0R next to_ tl **
      pure (l == value :: tl)

/// The ownership a freshly allocated cell has, stated over the two field values a C#
/// `new Cell<T> { ... }` supplies. Because R12.4 emits that as a record *literal*, the
/// caller needs no `with` binder to fold it.
unfold
let held (#a: Type0) (v: Class_Cell.class_Cell__opt a) (value: a) (next: Class_Cell.class_Cell__opt a)
  : slprop
  = B.pts_to v ({ Class_Cell.fld_value = value; Class_Cell.fld_next = next })

/// Push a cell the caller owns outright onto the front of a chain. This is `seg_intro_cons`
/// at the boundaries a whole chain has, and it is what lets a test *build* something to walk.
ghost fn seg_push (#a: Type0)
    (v: Class_Cell.class_Cell__opt a) (value: a) (next: Class_Cell.class_Cell__opt a) (l: list a)
  requires held v value next ** whole next l
  ensures  whole v (value :: l)
{
  seg_intro_cons v value next B.null l;
}

/// The shape a C# `[Ensures]` can name. `opened` fixes the two field values, which is what
/// the *step* needs -- the new split point is the `next` field, a value that exists only once
/// the heap has been read -- but a C# postcondition cannot bind an existential. So the
/// elimination lemma promises this, and the C# body picks the witnesses up by *reading the
/// fields*: `unfold` means Pulse sees through it, auto-eliminates the two existentials at the
/// call site, and the reads then produce exactly the terms `seg_advance` takes back as
/// ordinary arguments.
unfold
let opened_some (#a: Type0) (from: Class_Cell.class_Cell__opt a)
                (to_: Class_Cell.class_Cell__opt a) (l: list a)
  : slprop
  = exists* (value: a) (next: Class_Cell.class_Cell__opt a). opened from value next to_ l

/// The loop condition, stated once so that no C# body has to reason about it. `seg_cases`
/// ties the null test to the *shape* of the suffix; this ties it to the *counter*, which is
/// what a loop invariant indexed by `take`/`drop` actually needs.
ghost fn seg_at_end (#a: Type0) (from: Class_Cell.class_Cell__opt a) (i: int) (l: list a)
  preserves seg from B.null (CL.drop l i)
  requires pure (0 <= i /\ i <= L.length l)
  ensures  pure ((B.is_null from <==> i == L.length l) /\
                 (not (B.is_null from) <==> Cons? (CL.drop l i)))
{
  drop_cons_iff l i;
  seg_cases from (CL.drop l i);
}

/// Start the walk. `take l 0` is `[]` and `drop l 0` is `l`, so the loop is entered with
/// `cur = head` and `i = 0` and the invariant holds by construction.
ghost fn seg_start (#a: Type0) (head: Class_Cell.class_Cell__opt a) (l: list a)
  requires whole head l
  ensures  seg head head (CL.take l 0) ** seg head B.null (CL.drop l 0)
{
  seg_nil head;
  rewrite (cell_seg 1.0R head head ([] <: list a))
       as (cell_seg 1.0R head head (CL.take l 0));
  rewrite (cell_seg 1.0R head B.null l)
       as (cell_seg 1.0R head B.null (CL.drop l 0));
}

/// Open the first cell of a non-empty suffix. Every `rewrite` the elimination needs stays
/// inside; what comes out is `opened`, whose two field values the C# body then reads.
ghost fn seg_open (#a: Type0) (from: Class_Cell.class_Cell__opt a) (l: list a)
  requires whole from l ** pure (Cons? l)
  ensures  opened_some from B.null l
{
  rewrite (cell_seg 1.0R from B.null l) as (cell_seg 1.0R from B.null (L.hd l :: L.tl l));
  unfold (cell_seg 1.0R from B.null (L.hd l :: L.tl l));
  with r. assert (B.pts_to from #1.0R r);
  rewrite (B.pts_to from #1.0R r)
       as (B.pts_to from ({ Class_Cell.fld_value = r.Class_Cell.fld_value; Class_Cell.fld_next = r.Class_Cell.fld_next }));
  fold (opened from r.Class_Cell.fld_value r.Class_Cell.fld_next B.null l);
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
    (head from: Class_Cell.class_Cell__opt a)
    (value: a) (next: Class_Cell.class_Cell__opt a) (i: int) (l: list a)
  requires seg head from (CL.take l i) **
           opened from value next B.null (CL.drop l i) **
           pure (0 <= i /\ i < L.length l)
  ensures  seg head next (CL.take l (i + 1)) **
           seg next B.null (CL.drop l (i + 1)) **
           pure ((0 <= i /\ i < L.length l) ==> value == L.index l i)
{
  drop_step l i;
  take_step l i;
  unfold (opened from value next B.null (CL.drop l i));
  with tl. assert (cell_seg 1.0R next B.null tl);
  rewrite (cell_seg 1.0R next B.null tl)
       as (cell_seg 1.0R next B.null (CL.drop l (i + 1)));
  seg_snoc head from value next (CL.take l i);
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
    (head from: Class_Cell.class_Cell__opt a) (i: int) (l: list a)
  requires seg head from (CL.take l i) ** seg from B.null (CL.drop l i)
  ensures  whole head l
{
  seg_append head from B.null (CL.take l i) (CL.drop l i);
  CL.take_drop l i;
  rewrite (cell_seg 1.0R head B.null (L.append (CL.take l i) (CL.drop l i)))
       as (cell_seg 1.0R head B.null l);
}

/// Reaching `null` ends the walk: the counter has arrived at the length, and the list comes
/// back whole.
ghost fn seg_finish (#a: Type0)
    (head from: Class_Cell.class_Cell__opt a) (i: int) (l: list a)
  requires seg head from (CL.take l i) **
           seg from B.null (CL.drop l i) **
           pure (0 <= i /\ i <= L.length l /\ B.is_null from)
  ensures  whole head l ** pure (i == L.length l)
{
  seg_at_end from i l;
  seg_close head from i l;
}

