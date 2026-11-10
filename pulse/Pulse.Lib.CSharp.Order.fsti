module Pulse.Lib.CSharp.Order

/// The order a comparer decides (doc/translation.md R22.30). Every `val` here is a
/// MODELING AXIOM (R22.24): that `Comparer<T>.Default.Compare` -- or the `IComparer<T>`
/// a collection was given, which the collection's contract names by a ghost `comparer`
/// value -- is a deterministic total preorder. Only the sign of a comparison matters.

/// A comparer, as the specification sees it: its comparison function.
val comparer (t: Type) : Type0

/// `Comparer<T>.Default`.
val default_comparer (t: Type) : comparer t

/// `Comparer<T>.Default` is never the null reference (R27.56).
val default_comparer_not_null (t: Type)
  : Lemma (not (Pulse.Lib.CSharp.Null.is_null (default_comparer t)))
          [SMTPat (default_comparer t)]

/// `c.Compare(x, y)`, up to sign.
val compare (#t: Type) (c: comparer t) (x y: t) : int

let lt (#t: Type) (c: comparer t) (x y: t) : prop = compare c x y < 0
let le (#t: Type) (c: comparer t) (x y: t) : prop = compare c x y <= 0
let eq (#t: Type) (c: comparer t) (x y: t) : prop = compare c x y == 0

val compare_refl (#t: Type) (c: comparer t) (x: t)
  : Lemma (compare c x x == 0) [SMTPat (compare c x x)]

val compare_antisym (#t: Type) (c: comparer t) (x y: t)
  : Lemma ((compare c x y < 0 <==> compare c y x > 0) /\
           (compare c x y == 0 <==> compare c y x == 0))
          [SMTPat (compare c x y)]

val compare_trans (#t: Type) (c: comparer t) (x y z: t)
  : Lemma (requires compare c x y <= 0 /\ compare c y z <= 0)
          (ensures compare c x z <= 0 /\
                   ((compare c x y < 0 \/ compare c y z < 0) ==> compare c x z < 0))
