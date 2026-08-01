module Pulse.Lib.CSharp.Seq

/// Specification-level sequences.
///
/// `Pal.Contents(a)` in a C# specification denotes the `Seq.seq` value that the
/// array's `pts_to` resource holds, so everything a user can say about array
/// contents is ultimately said with `FStar.Seq`.
///
/// This module is where proof difficulty that the emitter must not invent
/// (doc/translation.md §0, rule 3) is allowed to live — but only as
/// *general-purpose* lemmas, phrased over arbitrary sequences and never over a
/// particular program. Nothing here mentions sorting, searching or any other
/// algorithm.

module Seq = FStar.Seq
open FStar.Seq

/// `Pal.IsPermutation(s1, s2)`.
let is_permutation (#a:eqtype) (s1 s2: Seq.seq a) : prop =
  Seq.permutation a s1 s2

// ---------------------------------------------------------------------------
// `is_permutation` is an equivalence. Each is immediate from the `count`-based
// definition, but stating them saves every client from rediscovering that.
// ---------------------------------------------------------------------------

let is_permutation_refl (#a:eqtype) (s: Seq.seq a)
  : Lemma (is_permutation s s)
          [SMTPat (is_permutation s s)]
  = ()

let is_permutation_sym (#a:eqtype) (s1 s2: Seq.seq a)
  : Lemma (requires is_permutation s1 s2)
          (ensures  is_permutation s2 s1)
  = ()

let is_permutation_trans (#a:eqtype) (s1 s2 s3: Seq.seq a)
  : Lemma (requires is_permutation s1 s2 /\ is_permutation s2 s3)
          (ensures  is_permutation s1 s3)
  = ()

let is_permutation_length (#a:eqtype) (s1 s2: Seq.seq a)
  : Lemma (requires is_permutation s1 s2)
          (ensures  Seq.length s1 == Seq.length s2)
  = Seq.perm_len s1 s2

// ---------------------------------------------------------------------------
// Swapping.
// ---------------------------------------------------------------------------

let swap_is_permutation (#a:eqtype) (s: Seq.seq a)
                        (i: nat { i < Seq.length s })
                        (j: nat { i <= j /\ j < Seq.length s })
  : Lemma (is_permutation s (Seq.swap s i j))
  = Seq.lemma_swap_permutes s i j

/// Overwriting a cell and then reading the *old* value of a neighbour into it
/// is a transposition.
///
/// This is the general fact behind any loop that moves an element through an
/// array one step at a time while a copy of it is held in a local: `s` is the
/// array, `x` is the value held in the local, `Seq.upd s (j+1) x` is the
/// "virtual" array that the local is conceptually part of, and one shift step
/// transposes two of its cells. Stated over arbitrary `s`, `j` and `x`, with no
/// reference to why the shifting is being done.
let upd_shift_is_swap (#a:Type) (s: Seq.seq a) (j: nat { j + 1 < Seq.length s }) (x: a)
  : Lemma (Seq.upd (Seq.upd s (j + 1) (Seq.index s j)) j x
           == Seq.swap (Seq.upd s (j + 1) x) j (j + 1))
  = Seq.lemma_eq_intro
      (Seq.upd (Seq.upd s (j + 1) (Seq.index s j)) j x)
      (Seq.swap (Seq.upd s (j + 1) x) j (j + 1))

/// The composite step, in the form a loop invariant actually needs it.
let upd_shift_is_permutation (#a:eqtype) (s: Seq.seq a)
                             (j: nat { j + 1 < Seq.length s }) (x: a)
  : Lemma (is_permutation (Seq.upd s (j + 1) x)
                          (Seq.upd (Seq.upd s (j + 1) (Seq.index s j)) j x))
  = upd_shift_is_swap s j x;
    Seq.lemma_swap_permutes (Seq.upd s (j + 1) x) j (j + 1)

// ---------------------------------------------------------------------------
// Framing: writing outside a range leaves the range alone. Needed by every
// loop invariant that speaks about a prefix or a suffix of an array.
// ---------------------------------------------------------------------------

let upd_outside_slice (#a:Type) (s: Seq.seq a)
                      (i: nat { i < Seq.length s }) (x: a)
                      (lo: nat) (hi: nat { lo <= hi /\ hi <= Seq.length s })
  : Lemma (requires i < lo \/ hi <= i)
          (ensures  Seq.slice (Seq.upd s i x) lo hi == Seq.slice s lo hi)
  = Seq.lemma_eq_intro (Seq.slice (Seq.upd s i x) lo hi) (Seq.slice s lo hi)

let upd_preserves_length (#a:Type) (s: Seq.seq a) (i: nat { i < Seq.length s }) (x: a)
  : Lemma (Seq.length (Seq.upd s i x) == Seq.length s)
          [SMTPat (Seq.length (Seq.upd s i x))]
  = ()

/// Writing a cell's own value back is a no-op. Trivial, but without it any
/// invariant phrased over `Seq.upd s i x` fails to *establish* at the point
/// where `x` was just read out of `s` at `i` -- which is every loop that lifts
/// an element into a local before moving it.
let upd_same (#a:Type) (s: Seq.seq a) (i: nat { i < Seq.length s })
  : Lemma (Seq.upd s i (Seq.index s i) == s)
          [SMTPat (Seq.upd s i (Seq.index s i))]
  = Seq.lemma_eq_intro (Seq.upd s i (Seq.index s i)) s
