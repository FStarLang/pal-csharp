module DllSeg
#lang-pulse

open Pulse
module B = Pulse.Lib.Box
module I32 = FStar.Int32
module L = FStar.List.Tot

/// `dll_seg p from prev to_ last l` owns the nodes `from`, ..., `last` -- and nothing
/// else -- holding the values `l`, where
///
///   * `from` is the first node of the segment, or `to_` if the segment is empty;
///   * `prev` is what the first node's `prev` field must equal -- the left boundary;
///   * `to_` is one *past* the last node: the segment does not own it;
///   * `last` is the final node, whose `next` is `to_`, or `prev` if the segment is empty.
///
/// Every back pointer is *constrained* by a `pure` equation rather than owned, because the
/// cell it points at is already owned by the node before it. Owning it twice is exactly the
/// unsoundness the equations avoid, and it is why a `prev` field can never be folded over.
let rec dll_seg (p: perm) ([@@@mkey] from: Class_DNode.class_DNode__opt)
                (prev: Class_DNode.class_DNode__opt) (to_: Class_DNode.class_DNode__opt)
                (last: Class_DNode.class_DNode__opt) (l: list int)
  : Tot slprop (decreases l)
  = match l with
    | [] -> pure (from == to_ /\ prev == last)
    | hd :: tl ->
      exists* (r: Class_DNode.class_DNode__raw).
        B.pts_to from #p r **
        pure (hd == I32.v r.Class_DNode.fld_value /\ r.Class_DNode.fld_prev == prev) **
        dll_seg p r.Class_DNode.fld_next from to_ last tl

/// The two shapes C# names. `unfold` so that slprop matching -- which is syntactic -- sees
/// `dll_seg` itself, and every lemma below applies to a contract written in terms of these.
unfold
let seg (from prev to_ last: Class_DNode.class_DNode__opt) (l: list int) : slprop =
  dll_seg 1.0R from prev to_ last l

/// A whole list is the segment that runs off both ends.
unfold
let whole (head tail: Class_DNode.class_DNode__opt) (l: list int) : slprop =
  dll_seg 1.0R head B.null B.null tail l

ghost fn dll_seg_intro_nil (p: perm) (from: Class_DNode.class_DNode__opt)
    (prev: Class_DNode.class_DNode__opt)
  requires emp
  ensures dll_seg p from prev from prev []
{
  fold (dll_seg p from prev from prev []);
}

ghost fn dll_seg_elim_nil (p: perm) (from: Class_DNode.class_DNode__opt)
    (prev to_ last: Class_DNode.class_DNode__opt) (#l: list int)
  requires dll_seg p from prev to_ last l ** pure (l == [])
  ensures pure (from == to_ /\ prev == last)
{
  rewrite (dll_seg p from prev to_ last l) as (dll_seg p from prev to_ last []);
  unfold (dll_seg p from prev to_ last []);
}

/// A non-empty segment starts at a real node. Under R10.2 that conclusion is about the
/// pointer the caller already holds -- there is no second, ghost name for it -- and the
/// step that proves it is `B.pts_to_not_null`, a Pulse library lemma.
ghost fn dll_seg_some (p: perm) (from: Class_DNode.class_DNode__opt)
    (prev to_ last: Class_DNode.class_DNode__opt) (#l: list int)
  preserves dll_seg p from prev to_ last l
  requires pure (Cons? l)
  ensures pure (not (B.is_null from))
{
  match l {
    [] -> {
      unfold (dll_seg p from prev to_ last []);
      fold (dll_seg p from prev to_ last []);
    }
    hd :: tl -> {
      unfold (dll_seg p from prev to_ last (hd :: tl));
      with r. assert (B.pts_to from #p r);
      B.pts_to_not_null from;
      fold (dll_seg p from prev to_ last (hd :: tl));
    }
  }
}

ghost fn dll_seg_elim_cons (p: perm) (from: Class_DNode.class_DNode__opt)
    (prev to_ last: Class_DNode.class_DNode__opt) (#l: list int)
  requires dll_seg p from prev to_ last l ** pure (Cons? l)
  ensures exists* (r: Class_DNode.class_DNode__raw) (tl: list int).
    B.pts_to from #p r **
    dll_seg p r.Class_DNode.fld_next from to_ last tl **
    pure (l == I32.v r.Class_DNode.fld_value :: tl /\ r.Class_DNode.fld_prev == prev)
{
  match l {
    [] -> {
      unfold (dll_seg p from prev to_ last []);
      unreachable ()
    }
    hd :: tl -> {
      unfold (dll_seg p from prev to_ last (hd :: tl));
      ()
    }
  }
}

/// Closing at the left. The node's own `prev` field supplies the new boundary, so a write
/// to `prev` costs no separate obligation: re-closing simply reports what the field holds.
ghost fn dll_seg_intro_cons (p: perm) (v: Class_DNode.class_DNode__opt)
    (to_ last: Class_DNode.class_DNode__opt)
    (#r: Class_DNode.class_DNode__raw) (#tl: list int)
  requires B.pts_to v #p r ** dll_seg p r.Class_DNode.fld_next v to_ last tl
  ensures dll_seg p v r.Class_DNode.fld_prev to_ last
            (I32.v r.Class_DNode.fld_value :: tl)
{
  fold (dll_seg p v r.Class_DNode.fld_prev to_ last
          (I32.v r.Class_DNode.fld_value :: tl));
}

/// Two adjacent segments make one. *This* is the lemma no `[Model]` could produce: it
/// relates two instances of the predicate across four boundary pointers, and it is proved
/// by induction on the first segment. It is what lets a loop walk a prefix and put it back.
ghost fn rec dll_seg_append (p: perm) (a: Class_DNode.class_DNode__opt)
    (pa: Class_DNode.class_DNode__opt) (b: Class_DNode.class_DNode__opt)
    (lb: Class_DNode.class_DNode__opt) (c: Class_DNode.class_DNode__opt)
    (lc: Class_DNode.class_DNode__opt) (#l1 #l2: list int)
  requires dll_seg p a pa b lb l1 ** dll_seg p b lb c lc l2
  ensures dll_seg p a pa c lc (L.append l1 l2)
  decreases l1
{
  match l1 {
    [] -> {
      dll_seg_elim_nil p a pa b lb #l1;
      rewrite (dll_seg p b lb c lc l2) as (dll_seg p a pa c lc (L.append l1 l2));
    }
    hd :: tl -> {
      dll_seg_elim_cons p a pa b lb #l1;
      with r tl'. assert (dll_seg p r.Class_DNode.fld_next a b lb tl');
      dll_seg_append p r.Class_DNode.fld_next a b lb c lc #tl' #l2;
      dll_seg_intro_cons p a c lc #r #(L.append tl' l2);
      rewrite (dll_seg p a r.Class_DNode.fld_prev c lc
                 (I32.v r.Class_DNode.fld_value :: L.append tl' l2))
           as (dll_seg p a pa c lc (L.append l1 l2));
    }
  }
}

/// Extending a segment on the *right* -- the step an iterative traversal takes when it
/// advances its cursor, and what §10.7's refused iterative traversal was missing.
ghost fn dll_seg_snoc (p: perm) (a: Class_DNode.class_DNode__opt)
    (pa: Class_DNode.class_DNode__opt) (v: Class_DNode.class_DNode__opt)
    (c: Class_DNode.class_DNode__opt) (#l1: list int) (#r: Class_DNode.class_DNode__raw)
  requires dll_seg p a pa v c l1 ** B.pts_to v #p r **
           pure (r.Class_DNode.fld_prev == c)
  ensures dll_seg p a pa r.Class_DNode.fld_next v
            (L.append l1 [I32.v r.Class_DNode.fld_value])
{
  dll_seg_intro_nil p r.Class_DNode.fld_next v;
  dll_seg_intro_cons p v r.Class_DNode.fld_next v #r #[];
  rewrite (dll_seg p v r.Class_DNode.fld_prev r.Class_DNode.fld_next v
             (I32.v r.Class_DNode.fld_value :: []))
       as (dll_seg p v c r.Class_DNode.fld_next v
             [I32.v r.Class_DNode.fld_value]);
  dll_seg_append p a pa v c r.Class_DNode.fld_next v #l1
    #[I32.v r.Class_DNode.fld_value];
}

/// The `if (x == null)` connection, and the restriction on it is the point: this holds only
/// when the right boundary is `null`, that is only for a *whole list*. For a general segment
/// emptiness is `from == to_`, decided by comparing the cursor with the boundary and not
/// with null. §12 therefore refuses to derive this and makes the user state and prove it.
ghost fn dll_cases (p: perm) (from: Class_DNode.class_DNode__opt)
    (prev: Class_DNode.class_DNode__opt) (last: Class_DNode.class_DNode__opt)
    (#l: list int)
  preserves dll_seg p from prev B.null last l
  ensures pure (not (B.is_null from) <==> Cons? l)
{
  match l {
    [] -> {
      unfold (dll_seg p from prev B.null last []);
      fold (dll_seg p from prev B.null last []);
    }
    hd :: tl -> {
      unfold (dll_seg p from prev B.null last (hd :: tl));
      with r. assert (B.pts_to from #p r);
      B.pts_to_not_null from;
      fold (dll_seg p from prev B.null last (hd :: tl));
    }
  }
}

// ===========================================================================
// The C# face: one lemma per step a C# body takes
// ===========================================================================
//
// Everything above is faithful Pulse, and none of it is usable as a *target*. Each of the
// elim lemmas hands back an existential record the caller must name with `with r tl.`, and
// each intro produces the segment at a non-null reference where the contract has the nullable
// cursor `from`, so the caller must `rewrite` between them. Neither step is one the user
// chose: both are artefacts of how `dll_seg`'s cons case happens to be written.
//
// So this section publishes, for each step a C# body actually takes, one ghost function
// whose signature mentions only what C# can name -- a parameter, a local, `null`, a spec
// list -- and keeps every `with` and every `rewrite` inside. That is §12's style rule, and
// what a `[Lemma]` declared over `SlProp` in `Dll.cs` binds to.
//
// R10.2 removed the second half of that job. The cursor used to have to be passed twice --
// once nullable, once not -- because the two were different Pulse types; now they are one,
// so each of these lemmas takes the cursor once, exactly as the C# does.
//
// Pinned first, and independently, by test/pulse_facts/SegmentFacts.fst §6.

/// `opened from v prev to_ last l` is `seg from prev to_ last l` with its first node
/// unfolded: the node's cell is owned outright and the rest of the segment hangs off its
/// `next` field.
///
/// It names the head node *once*. Before R10.2 it had to name it twice -- as the nullable
/// cursor the contract talks about, and as the non-null reference a field access reads
/// through -- with a `pure` tying them together, because those were two Pulse types for one
/// C# variable. They are now one type, so the `pts_to` is already syntactically at the
/// cursor the caller passed and the tying `pure` has nothing left to say.
unfold
let opened (from: Class_DNode.class_DNode__opt)
           (prev to_ last: Class_DNode.class_DNode__opt) (l: list int)
  : slprop
  = exists* (r: Class_DNode.class_DNode__raw) (tl: list int).
      B.pts_to from r **
      dll_seg 1.0R r.Class_DNode.fld_next from to_ last tl **
      pure (l == I32.v r.Class_DNode.fld_value :: tl /\
            r.Class_DNode.fld_prev == prev)

/// `cell v value prev next` is the ownership a freshly allocated node has, stated over the
/// three field values a C# `new DNode { ... }` supplies. Because R10.1 emits that as a
/// record *literal*, the caller needs no `with` binder to fold it.
///
/// `value` is the *mathematical* integer, not the machine one, because R4.13 sends a C#
/// `int` into a specification as its `.v`. The machine value is existential here for
/// exactly that reason, and the `pure` ties the two together.
unfold
let cell (v: Class_DNode.class_DNode__opt) (value: int)
         (prev next: Class_DNode.class_DNode__opt)
  : slprop
  = exists* (x: I32.t).
      B.pts_to v ({ Class_DNode.fld_value = x; fld_prev = prev; fld_next = next }) **
      pure (I32.v x == value)

/// Open the first node of a non-empty segment.
ghost fn seg_open (from: Class_DNode.class_DNode__opt)
    (prev to_ last: Class_DNode.class_DNode__opt) (l: list int)
  requires seg from prev to_ last l ** pure (Cons? l)
  ensures  opened from prev to_ last l
{
  dll_seg_elim_cons 1.0R from prev to_ last #l;
}

/// Close the first node again. The segment's left boundary is read off the node's own
/// `prev` field, so a C# body that just *wrote* that field closes at the new value -- which
/// is why the write needs no obligation of its own.
ghost fn seg_close (from: Class_DNode.class_DNode__opt)
    (prev to_ last: Class_DNode.class_DNode__opt) (l: list int)
  requires opened from prev to_ last l
  ensures  seg from prev to_ last l
{
  with r tl. assert (dll_seg 1.0R r.Class_DNode.fld_next from to_ last tl);
  dll_seg_intro_cons 1.0R from to_ last #r #tl;
  rewrite (dll_seg 1.0R from r.Class_DNode.fld_prev to_ last
             (I32.v r.Class_DNode.fld_value :: tl))
       as (dll_seg 1.0R from prev to_ last l);
}

/// Push a node the caller owns outright onto the front of a segment: `dll_seg_intro_cons`
/// restated over `cell`, so that the three field values are named rather than projected out
/// of an existential record.
ghost fn seg_cons (v: Class_DNode.class_DNode__opt) (value: int)
    (prev next to_ last: Class_DNode.class_DNode__opt) (l: list int)
  requires cell v value prev next ** seg next v to_ last l
  ensures  seg v prev to_ last (value :: l)
{
  with x. assert (B.pts_to v
    ({ Class_DNode.fld_value = x; fld_prev = prev; fld_next = next }));
  dll_seg_intro_cons 1.0R v to_ last
    #({ Class_DNode.fld_value = x; fld_prev = prev; fld_next = next }) #l;
  rewrite (dll_seg 1.0R v prev to_ last (I32.v x :: l))
       as (dll_seg 1.0R v prev to_ last (value :: l));
}
