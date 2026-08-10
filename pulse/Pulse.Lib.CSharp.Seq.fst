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
module Math = FStar.Math.Lemmas
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

// ---------------------------------------------------------------------------
// Rotation. A ring buffer stores its elements starting at an arbitrary offset
// and wrapping round, so its abstraction function is "read `s` from `n`,
// wrapping" -- and that is a fact about sequences, not about ring buffers.
// Stated here over arbitrary `s` and `n`, with no reference to why anyone would
// want it.
// ---------------------------------------------------------------------------

/// `Pal.Rotate(s, n)`.
let rotate (#a:Type) (s: Seq.seq a) (n: nat) : Seq.seq a =
  if Seq.length s = 0 then s
  else
    let m = n % Seq.length s in
    Seq.append (Seq.slice s m (Seq.length s)) (Seq.slice s 0 m)

let rotate_length (#a:Type) (s: Seq.seq a) (n: nat)
  : Lemma (Seq.length (rotate s n) == Seq.length s)
          [SMTPat (Seq.length (rotate s n))]
  = ()

/// The characteristic equation, and the only thing a client ever needs: reading
/// the rotation at `k` is reading the original at `n + k`, modulo the length.
/// The pattern is on the left-hand side, so it fires exactly where a
/// specification mentions a rotated element.
let rotate_index (#a:Type) (s: Seq.seq a) (n: nat) (k: nat { k < Seq.length s })
  : Lemma (Seq.index (rotate s n) k == Seq.index s ((n + k) % Seq.length s))
          [SMTPat (Seq.index (rotate s n) k)]
  = let len = Seq.length s in
    let m = n % len in
    let front = Seq.slice s m len in
    let back = Seq.slice s 0 m in
    if k < len - m
    then begin
      Seq.lemma_index_app1 front back k;
      Seq.lemma_index_slice s m len k;
      Math.lemma_mod_plus_distr_l n k len;
      Math.small_mod (m + k) len
    end
    else begin
      Seq.lemma_index_app2 front back k;
      Seq.lemma_index_slice s 0 m (k - (len - m));
      Math.lemma_mod_plus_distr_l n k len;
      Math.lemma_mod_sub (m + k) len 1
    end

// ---------------------------------------------------------------------------
// `Pal.Splice(v, from, to, w)`: the contents of a parent after a borrowed window
// `[from, to)` is given back holding `w`.
//
// This is the only new spec-level vocabulary `Span<T>` needs (doc/translation.md
// R17.8). It is total, with the parent returned unchanged on ill-formed arguments,
// so that it can appear in a specification without dragging a refinement along;
// every lemma below carries the well-formedness hypotheses instead.
// ---------------------------------------------------------------------------

let splice (#t: Type0) (v: Seq.seq t) (i j: nat) (w: Seq.seq t) : Seq.seq t =
  if i <= j && j <= Seq.length v && Seq.length w = j - i
  then Seq.append (Seq.slice v 0 i) (Seq.append w (Seq.slice v j (Seq.length v)))
  else v

let splice_length (#t: Type0) (v: Seq.seq t) (i j: nat) (w: Seq.seq t)
  : Lemma (requires i <= j /\ j <= Seq.length v /\ Seq.length w == j - i)
          (ensures  Seq.length (splice v i j w) == Seq.length v)
          [SMTPat (Seq.length (splice v i j w))]
  = ()

/// Pointwise: inside the window the parent shows the window's contents, outside it
/// the parent is untouched. This is what every postcondition about an array that was
/// written through a span ultimately reduces to, so it is patterned.
let splice_index (#t: Type0) (v: Seq.seq t) (i j: nat) (w: Seq.seq t) (k: nat)
  : Lemma (requires i <= j /\ j <= Seq.length v /\ Seq.length w == j - i /\ k < Seq.length v)
          (ensures  Seq.index (splice v i j w) k ==
                    (if i <= k && k < j then Seq.index w (k - i) else Seq.index v k))
          [SMTPat (Seq.index (splice v i j w) k)]
  = ()

/// A window given back unwritten leaves the parent exactly as it was, so a read-only
/// borrow costs its user nothing. Not patterned: the trigger would be the same as
/// `splice_index`'s and it is only wanted where a whole borrow is being collapsed.
let splice_same (#t: Type0) (v: Seq.seq t) (i j: nat)
  : Lemma (requires i <= j /\ j <= Seq.length v)
          (ensures  splice v i j (Seq.slice v i j) == v)
  = Seq.lemma_eq_intro (splice v i j (Seq.slice v i j)) v

/// The whole of a parent, which is what `a.AsSpan(0, a.Length)` borrows.
let splice_all (#t: Type0) (v: Seq.seq t) (w: Seq.seq t)
  : Lemma (requires Seq.length w == Seq.length v)
          (ensures  splice v 0 (Seq.length v) w == w)
  = Seq.lemma_eq_intro (splice v 0 (Seq.length v) w) w
