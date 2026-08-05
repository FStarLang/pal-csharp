using System;
using PalLang;

// §12. A doubly linked list, specified by *list segments*.
//
// This is the case §10's `[Model]` scheme cannot reach. §10 derives a class's ownership
// predicate from one downward fold over one recursive field. A segment is bounded at both
// ends, so it carries two boundary pointers no fold over the fields could produce; its
// empty case is `from == to_`, a relation between two of those boundaries rather than a
// property of one; and its central lemma -- that two adjacent segments compose -- relates
// two instances of the predicate at once.
//
// So the predicate is the user's. `DNode` below is `[Plain]`: the translator emits its
// representation and stops. Everything else -- the predicate, its intro and elim lemmas,
// and the segment-append lemma -- is written here in Pulse and named from C#.
//
// Pinned first, and independently, by test/pulse_facts/SegmentFacts.fst.
[assembly: IncludePulse("DllSeg", """
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
      exists* (v: Class_DNode.class_DNode) (r: Class_DNode.class_DNode__raw).
        pure (from == Some v) **
        B.pts_to v #p r **
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
  dll_seg 1.0R head None None tail l

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

/// A non-empty segment starts at a real node. This is its own step because the `Some?`
/// refinement is what lets `elim_cons` name the node as `Some?.v from` -- a *program*
/// pointer the C# body can read a field of -- rather than as a ghost existential.
ghost fn dll_seg_some (p: perm) (from: Class_DNode.class_DNode__opt)
    (prev to_ last: Class_DNode.class_DNode__opt) (#l: list int)
  preserves dll_seg p from prev to_ last l
  requires pure (Cons? l)
  ensures pure (Some? from)
{
  match l {
    [] -> {
      unfold (dll_seg p from prev to_ last []);
      fold (dll_seg p from prev to_ last []);
    }
    hd :: tl -> {
      unfold (dll_seg p from prev to_ last (hd :: tl));
      with v r. assert (B.pts_to v #p r);
      fold (dll_seg p from prev to_ last (hd :: tl));
    }
  }
}

ghost fn dll_seg_elim_cons (p: perm) (from: Class_DNode.class_DNode__opt { Some? from })
    (prev to_ last: Class_DNode.class_DNode__opt) (#l: list int)
  requires dll_seg p from prev to_ last l ** pure (Cons? l)
  ensures exists* (r: Class_DNode.class_DNode__raw) (tl: list int).
    B.pts_to (Some?.v from) #p r **
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
      with v r. assert (B.pts_to v #p r);
      rewrite each v as (Some?.v from);
    }
  }
}

/// Closing at the left. The node's own `prev` field supplies the new boundary, so a write
/// to `prev` costs no separate obligation: re-closing simply reports what the field holds.
ghost fn dll_seg_intro_cons (p: perm) (v: Class_DNode.class_DNode)
    (to_ last: Class_DNode.class_DNode__opt)
    (#r: Class_DNode.class_DNode__raw) (#tl: list int)
  requires B.pts_to v #p r ** dll_seg p r.Class_DNode.fld_next (Some v) to_ last tl
  ensures dll_seg p (Some v) r.Class_DNode.fld_prev to_ last
            (I32.v r.Class_DNode.fld_value :: tl)
{
  fold (dll_seg p (Some v) r.Class_DNode.fld_prev to_ last
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
      dll_seg_some p a pa b lb #l1;
      dll_seg_elim_cons p a pa b lb #l1;
      with r tl'. assert (dll_seg p r.Class_DNode.fld_next a b lb tl');
      dll_seg_append p r.Class_DNode.fld_next a b lb c lc #tl' #l2;
      dll_seg_intro_cons p (Some?.v a) c lc #r #(L.append tl' l2);
      rewrite (dll_seg p (Some (Some?.v a)) r.Class_DNode.fld_prev c lc
                 (I32.v r.Class_DNode.fld_value :: L.append tl' l2))
           as (dll_seg p a pa c lc (L.append l1 l2));
    }
  }
}

/// Extending a segment on the *right* -- the step an iterative traversal takes when it
/// advances its cursor, and what §10.7's refused iterative traversal was missing.
ghost fn dll_seg_snoc (p: perm) (a: Class_DNode.class_DNode__opt)
    (pa: Class_DNode.class_DNode__opt) (v: Class_DNode.class_DNode)
    (c: Class_DNode.class_DNode__opt) (#l1: list int) (#r: Class_DNode.class_DNode__raw)
  requires dll_seg p a pa (Some v) c l1 ** B.pts_to v #p r **
           pure (r.Class_DNode.fld_prev == c)
  ensures dll_seg p a pa r.Class_DNode.fld_next (Some v)
            (L.append l1 [I32.v r.Class_DNode.fld_value])
{
  dll_seg_intro_nil p r.Class_DNode.fld_next (Some v);
  dll_seg_intro_cons p v r.Class_DNode.fld_next (Some v) #r #[];
  rewrite (dll_seg p (Some v) r.Class_DNode.fld_prev r.Class_DNode.fld_next (Some v)
             (I32.v r.Class_DNode.fld_value :: []))
       as (dll_seg p (Some v) c r.Class_DNode.fld_next (Some v)
             [I32.v r.Class_DNode.fld_value]);
  dll_seg_append p a pa (Some v) c r.Class_DNode.fld_next (Some v) #l1
    #[I32.v r.Class_DNode.fld_value];
}

/// The `if (x == null)` connection, and the restriction on it is the point: this holds only
/// when the right boundary is `None`, that is only for a *whole list*. For a general segment
/// emptiness is `from == to_`, decided by comparing the cursor with the boundary and not
/// with null. §12 therefore refuses to derive this and makes the user state and prove it.
ghost fn dll_cases (p: perm) (from: Class_DNode.class_DNode__opt)
    (prev: Class_DNode.class_DNode__opt) (last: Class_DNode.class_DNode__opt)
    (#l: list int)
  preserves dll_seg p from prev None last l
  ensures pure (Some? from <==> Cons? l)
{
  match l {
    [] -> {
      unfold (dll_seg p from prev None last []);
      fold (dll_seg p from prev None last []);
    }
    hd :: tl -> {
      unfold (dll_seg p from prev None last (hd :: tl));
      with v r. assert (B.pts_to v #p r);
      fold (dll_seg p from prev None last (hd :: tl));
    }
  }
}
""")]

namespace PalCSharp.Tests;

/// <summary>
/// R12.1. A <c>[Plain]</c> class: the translator emits the record, the reference and the
/// nullable reference, and derives nothing else. There is no <c>[Model]</c> because there
/// is no abstraction function -- what a `DNode` means is only ever said by a predicate
/// that ranges over many of them at once.
/// </summary>
[Plain]
public sealed class DNode
{
    internal int value;
    internal DNode? prev;
    internal DNode? next;
}

/// <summary>
/// R12.2. The C# face of the user's predicate. An <c>SlProp</c>-valued <c>[SpecOp]</c> is
/// an *ownership* clause: where it appears in a <c>[Requires]</c> or <c>[Ensures]</c> it
/// joins the separating conjunction rather than the <c>pure</c>.
/// </summary>
public static class Dll
{
    /// <summary>The nodes from <paramref name="from"/> to <paramref name="last"/>.</summary>
    [SpecOp("DllSeg.seg")]
    public static SlProp Seg(DNode? from, DNode? prev, DNode? to, DNode? last,
                             SpecList<SpecInt> values) => throw new InvalidOperationException();

    /// <summary>A whole list: the segment that runs off both ends.</summary>
    [SpecOp("DllSeg.whole")]
    public static SlProp Whole(DNode? head, DNode? tail, SpecList<SpecInt> values)
        => throw new InvalidOperationException();
}
