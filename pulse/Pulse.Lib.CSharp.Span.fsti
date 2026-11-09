module Pulse.Lib.CSharp.Span
#lang-pulse

/// `System.Span<T>` and `System.ReadOnlySpan<T>`.
///
/// A span is a *borrowed window* onto memory somebody else owns. That is the whole
/// of its design in C# and the whole of its translation here: `Span<T>` is
/// a length-bounded `Pulse.Lib.Slice.slice T`, and the operations below are the C#-shaped face of
/// `Pulse.Lib.Slice`, exactly as `Pulse.Lib.CSharp.Array` is the C#-shaped face of
/// `Pulse.Lib.Array` — `int` indices instead of `size_t`, a non-ghost length, and
/// nothing else new.
///
/// The one thing this module adds that has no array analogue is the *receipt*.
/// Creating a span consumes the parent's `pts_to` and hands back the window's,
/// together with a token recording what was borrowed and from where. The parent is
/// unusable until the token is redeemed. Redeeming it is invisible in C# — it is a
/// proof step with no runtime content — so it is a ghost statement the user writes,
/// `Pal.Restore(w)`, and never something the translation infers. See
/// doc/translation.md §17, and `test/pulse_facts/SliceFacts.fst` S7–S9 for the
/// probes these signatures were derived from.
///
/// Three ways in, three ways back out:
///
/// | C# | creates | receipt | `Pal.Restore` |
/// |---|---|---|---|
/// | `Span<T> s = a;`, `a.AsSpan()` | `of_array` | `is_from_array a s` | `restore_array` |
/// | `a.AsSpan(i, n)` | `of_array_range` | `is_range_of a w _ i j _` | `restore_array_range` |
/// | `s.Slice(i, n)`, `s[i..j]` | `sub` | `is_sub_of s w _ i j _` | `restore_sub` |

open Pulse
open Pulse.Lib.CSharp.Assumptions
open Pulse.Lib.CSharp.Casts
open Pulse.Lib.CSharp.Inhabited
open Pulse.Lib.CSharp.Seq
open Pulse.Lib.SmallType

module A = Pulse.Lib.CSharp.Array
module S = Pulse.Lib.Slice
module I32 = FStar.Int32
module SZ = FStar.SizeT
module Seq = FStar.Seq

type span (t: Type0) = s: S.slice t { SZ.v (S.len s) < pow2 31 }

/// Keep the wrapper in the receipt's matching key, rather than trying to infer
/// the wrapper from its raw storage projection when restoring ownership.
val is_from_array (#t: Type0) (a: A.array t) (s: S.slice t) : slprop

/// `Slice.len` is executable; the refinement makes conversion to `int` safe.
val span_length (#t: Type0) (s: span t) : I32.t

val span_length_v (#t: Type0) (s: span t)
  : Lemma (I32.v (span_length s) == SZ.v (S.len s))
          [SMTPat (I32.v (span_length s))]

val span_length_bound (#t: Type0) (s: span t)
  : Lemma (SZ.v (S.len s) < pow2 31)
          [SMTPat (SZ.v (S.len s))]

/// `s.Length`. The `rewrites_to` is load-bearing for the same reason it is on
/// `arr_length` (R3.3): without it a loop guard `k < s.Length` has no pure form.
fn length_i32 (#t: Type0) (s: span t) (#p: perm) (#v: Ghost.erased (Seq.seq t))
  preserves S.pts_to s #p v
  returns  n : I32.t
  ensures  rewrites_to n (span_length s)
  ensures  pure (I32.v n == Seq.length v)

/// `s[i]`, at a C# `int` index. The caller owes both bounds (R6.4).
fn read (#t: Type0) (s: span t) (i: I32.t)
        (#p: perm)
        (#v: Ghost.erased (Seq.seq t) { I32.v i >= 0 /\ I32.v i < Seq.length v })
  preserves S.pts_to s #p v
  returns  x : t
  ensures  rewrites_to x (Seq.index v (I32.v i))

/// `s[i] = x`. There is no `ReadOnlySpan<T>` counterpart and none is needed: its
/// indexer returns `ref readonly T`, so C# itself rejects the assignment (R17.4).
fn write (#t: Type0) (s: span t) (i: I32.t) (x: t)
         (#v: Ghost.erased (Seq.seq t) { I32.v i >= 0 /\ I32.v i < Seq.length v })
  requires S.pts_to s v
  ensures  S.pts_to s (Seq.upd v (I32.v i) x)

(* ---------------------------------------------------------------------- *)
(* Borrowing a whole array.                                               *)
(* ---------------------------------------------------------------------- *)

/// `Span<T> s = a;` and `a.AsSpan()`.
///
/// `A.pts_to a` is gone from here until `restore_array`, which is the correct
/// reading of C#: while a span is out, writes through `a` and writes through `s`
/// are writes to the same memory, and no sound rule lets both be owned at once.
fn of_array (#t: Type0) (a: A.array t) (#p: perm) (#v: Ghost.erased (Seq.seq t))
  requires A.pts_to a #p v
  returns  s : span t
  ensures  S.pts_to s #p v
  ensures  is_from_array a s

/// `Pal.Restore(s)` for a span borrowed with `of_array`.
///
/// Note what is and is not explicit: the window is named, and the array, the
/// permission and both contents are recovered by unifying the receipt against the
/// context. That is what lets `Pal.Restore` take one argument, and it is the reason
/// the receipt has to be a resource rather than a compile-time note (S8).
ghost
fn restore_array (#t: Type0) (s: S.slice t)
                 (#a: A.array t) (#p: perm) (#v: Ghost.erased (Seq.seq t))
  requires S.pts_to s #p v
  requires is_from_array a s
  ensures  A.pts_to a #p v

(* ---------------------------------------------------------------------- *)
(* Borrowing a window of an array.                                        *)
(* ---------------------------------------------------------------------- *)

/// The receipt for `a.AsSpan(i, n)`.
///
/// `a.AsSpan(i, n)` is one C# construct, so it is one borrow, even though Pulse
/// takes it in two steps — `from_array` then `subslice` — with an intermediate
/// whole-array slice the C# program never names. That intermediate is existentially
/// quantified here so that one `Pal.Restore` redeems the whole thing (S9).
///
/// The window's length is part of the receipt because `restore_array_range` cannot
/// otherwise *state* its postcondition: `splice v i j v'` is the identity unless
/// `v'` is known to be `j - i` long, and after writes through the window that is a
/// fact about the borrow, not about `v'`.
val is_range_of (#t: Type0) (a: A.array t) (w: S.slice t) (p: perm) (i j: nat)
                (v: Seq.seq t { i <= j /\ j <= Seq.length v })
  : slprop

/// `a.AsSpan(i, n)`, with `j = i + n`.
fn of_array_range (#t: Type0) (a: A.array t) (i: I32.t) (n: I32.t)
                  (#p: perm)
                  (#v: Ghost.erased (Seq.seq t) { I32.v i >= 0 /\ I32.v n >= 0 /\
                                                  I32.v i + I32.v n <= Seq.length v })
  requires A.pts_to a #p v
  returns  w : span t
  ensures  S.pts_to w #p (Seq.slice v (I32.v i) (I32.v i + I32.v n))
  ensures  is_range_of a w p (I32.v i) (I32.v i + I32.v n) v

/// `Pal.Restore(w)` for a window of an array. The array afterwards holds the
/// window's *current* contents spliced between the two parts outside it, which are
/// unchanged: writes through the window are visible in the array, and `splice_same`
/// (`Pulse.Lib.CSharp.Seq`) collapses this to the identity when nothing was written.
ghost
fn restore_array_range (#t: Type0) (w: S.slice t)
                       (#a: A.array t) (#p: perm) (#i #j: nat)
                       (#v: Ghost.erased (Seq.seq t) { i <= j /\ j <= Seq.length v })
                       (#v': Ghost.erased (Seq.seq t))
  requires S.pts_to w #p v'
  requires is_range_of a w p i j v
  ensures  A.pts_to a #p (splice v i j v')

(* ---------------------------------------------------------------------- *)
(* Borrowing a window of a span.                                          *)
(* ---------------------------------------------------------------------- *)

/// The receipt for `s.Slice(i, n)` and `s[i..j]`. Windows nest: a window of a window
/// is an ordinary `sub`, and the receipts are redeemed innermost first, because the
/// outer one cannot be redeemed without the `pts_to` the inner one is holding.
val is_sub_of (#t: Type0) (s: S.slice t) (w: S.slice t) (p: perm) (i j: nat)
              (v: Seq.seq t { i <= j /\ j <= Seq.length v })
  : slprop

/// `s.Slice(i, n)` and `s[i .. i+n]`, with `j = i + n`.
fn sub (#t: Type0) (s: span t) (i: I32.t) (n: I32.t)
       (#p: perm)
       (#v: Ghost.erased (Seq.seq t) { I32.v i >= 0 /\ I32.v n >= 0 /\
                                       I32.v i + I32.v n <= Seq.length v })
  requires S.pts_to s #p v
  returns  w : span t
  ensures  S.pts_to w #p (Seq.slice v (I32.v i) (I32.v i + I32.v n))
  ensures  is_sub_of s w p (I32.v i) (I32.v i + I32.v n) v

/// `Pal.Restore(w)` for a window of a span.
ghost
fn restore_sub (#t: Type0) (w: S.slice t)
               (#s: S.slice t) (#p: perm) (#i #j: nat)
               (#v: Ghost.erased (Seq.seq t) { i <= j /\ j <= Seq.length v })
               (#v': Ghost.erased (Seq.seq t))
  requires S.pts_to w #p v'
  requires is_sub_of s w p i j v
  ensures  S.pts_to s #p (splice v i j v')

(* ---------------------------------------------------------------------- *)
(* Copying between spans.                                                 *)
(* ---------------------------------------------------------------------- *)

/// `src.CopyTo(dst)`. C# throws when `dst` is shorter; the length equality is a
/// proof obligation here, which is R6.4's treatment of every other C# check.
fn copy_to (#t: Type0) (src: S.slice t) (dst: S.slice t) (#p: perm)
           (#v: Ghost.erased (Seq.seq t))
  requires exists* v_dst. S.pts_to dst v_dst ** S.pts_to src #p v **
                          pure (Seq.length v_dst == Seq.length v)
  ensures  S.pts_to dst v ** S.pts_to src #p v
