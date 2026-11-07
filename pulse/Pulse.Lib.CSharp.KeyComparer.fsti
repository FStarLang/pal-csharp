module Pulse.Lib.CSharp.KeyComparer

/// A comparer of pairs that orders them by their first components (doc/translation.md
/// R27.58): `SortedDictionary<K, V>.KeyValuePairComparer`, over §25's comparer model
/// (`Pulse.Lib.CSharp.Order`). Pairs are `KeyValuePair<K, V>` (R29.1).

module O = Pulse.Lib.CSharp.Order
module S = Pulse.Lib.CSharp.Sorted

/// MODELING AXIOM (R27.58). The pair comparer whose key comparer is `c`.
val of_keys (k v: Type) (c: O.comparer k) : O.comparer (k & v)

/// MODELING AXIOM (R27.58). It compares the keys, and nothing else.
val compare_of_keys (#k #v: Type) (c: O.comparer k) (x y: k & v)
  : Lemma (O.compare (of_keys k v c) x y == O.compare c (fst x) (fst y))
          [SMTPat (O.compare (of_keys k v c) x y)]

/// MODELING AXIOM (R27.58). The key comparer of a pair comparer built by `of_keys`; what
/// `KeyValuePairComparer.keyComparer` holds.
val key_of (#k #v: Type) (c: O.comparer (k & v)) : O.comparer k

val key_of_keys (#k #v: Type) (c: O.comparer k)
  : Lemma (key_of (of_keys k v c) == c) [SMTPat (of_keys k v c)]

/// MODELING AXIOM (R27.58). The object `new KeyValuePairComparer(c)` builds is not the
/// null reference.
val of_keys_not_null (#k #v: Type) (c: O.comparer k)
  : Lemma (~ (S.is_null (of_keys k v c))) [SMTPat (of_keys k v c)]

/// `new KeyValuePairComparer(c)`: `c ?? Comparer<K>.Default` as a pair comparer.
let create (#k #v: Type) (c: O.comparer k) : O.comparer (k & v) = of_keys k v (S.or_default c)

/// `KeyValuePairComparer`, as a type: a pair comparer.
let pair_comparer (k v: Type) : Type0 = O.comparer (k & v)
