module SortedSetMerge

/// Steps of the enumerator walks SortedSet<T>'s merges (UnionWith, IntersectWith) make,
/// proved once here rather than in every arm of their loops.

module Seq = FStar.Seq

/// `p` is the suffix of `s` of its length: an enumerator over `s` has `p` still to yield.
/// Opaque, so that the merge loops' invariants do not equate an enumerator's pending items
/// with a slice of `s`: `MoveNext` slices the pending items, and with that equation every
/// such slice is a slice of a slice, which `Seq.slice_slice` rewrites over and over.
[@@"opaque_to_smt"]
let suffix (#t: Type0) (s p: Seq.seq t) : prop =
  Seq.length p <= Seq.length s /\
  Seq.equal p (Seq.slice s (Seq.length s - Seq.length p) (Seq.length s))

/// `s[i..]` and `s[..j]`, total: Pulse proves a `Seq.slice`'s bounds each time it checks a term
/// that holds one, and the merge loops' invariants and lemma calls hold several.
let drop (#t: Type0) (s: Seq.seq t) (i: int) : Seq.seq t =
  if 0 <= i && i <= Seq.length s then Seq.slice s i (Seq.length s) else Seq.empty

let take (#t: Type0) (s: Seq.seq t) (j: int) : Seq.seq t =
  if 0 <= j && j <= Seq.length s then Seq.slice s 0 j else Seq.empty

/// The whole of `s` is a suffix of `s`: an enumerator before its first `MoveNext`.
let suffix_whole (#t: Type0) (s: Seq.seq t) : Lemma (suffix s s) =
  reveal_opaque (`%suffix) (suffix #t)

/// An enumerator over `s` whose pending items `p0` are a suffix of `s`: what holds of the
/// pending items `MoveNext` leaves (`p0[(moved ? 1 : 0)..]`), and of the item it moves to.
let pending_next (#t: Type0) (s p0: Seq.seq t)
  : Lemma (requires suffix s p0)
          (ensures Seq.length p0 <= Seq.length s /\
                   Seq.length (Seq.slice p0 0 (Seq.length p0)) == Seq.length p0 /\
                   suffix s (Seq.slice p0 0 (Seq.length p0)) /\
                   (Seq.length p0 > 0 ==>
                     Seq.length (Seq.slice p0 1 (Seq.length p0)) + 1 == Seq.length p0 /\
                     suffix s (Seq.slice p0 1 (Seq.length p0)) /\
                     Seq.index p0 0 == Seq.index s (Seq.length s - Seq.length (Seq.slice p0 1 (Seq.length p0)) - 1)))
  = reveal_opaque (`%suffix) (suffix #t);
    assert (Seq.equal (Seq.slice p0 0 (Seq.length p0)) p0)
