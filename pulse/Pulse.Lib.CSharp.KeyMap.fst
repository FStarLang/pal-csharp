module Pulse.Lib.CSharp.KeyMap

/// A sequence of pairs ordered by `KeyComparer.of_keys c` is a map from keys to values
/// (doc/translation.md R27.58): its searches are searches of its keys under `c`. Proved
/// from `Pulse.Lib.CSharp.KeyComparer`'s axioms.

module Seq = FStar.Seq
module O = Pulse.Lib.CSharp.Order
module S = Pulse.Lib.CSharp.Sorted
module KC = Pulse.Lib.CSharp.KeyComparer

/// The keys of `s`, in order.
let keys (#k #v: Type) (s: Seq.seq (k & v)) : Seq.seq k =
  Seq.init (Seq.length s) (fun i -> fst (Seq.index s i))

let keys_length (#k #v: Type) (s: Seq.seq (k & v))
  : Lemma (Seq.length (keys s) == Seq.length s) [SMTPat (keys s)]
  = ()

let keys_index (#k #v: Type) (s: Seq.seq (k & v)) (i: nat)
  : Lemma (requires i < Seq.length s)
          (ensures Seq.index (keys s) i == fst (Seq.index s i))
          [SMTPat (Seq.index (keys s) i)]
  = ()

/// R32.11. The values of `s`, in key order.
let values (#k #v: Type) (s: Seq.seq (k & v)) : Seq.seq v =
  Seq.init (Seq.length s) (fun i -> snd (Seq.index s i))

let values_length (#k #v: Type) (s: Seq.seq (k & v))
  : Lemma (Seq.length (values s) == Seq.length s) [SMTPat (values s)]
  = ()

let values_index (#k #v: Type) (s: Seq.seq (k & v)) (i: nat)
  : Lemma (requires i < Seq.length s)
          (ensures Seq.index (values s) i == snd (Seq.index s i))
          [SMTPat (Seq.index (values s) i)]
  = ()

let keys_tail (#k #v: Type) (s: Seq.seq (k & v))
  : Lemma (requires Seq.length s > 0)
          (ensures keys (Seq.tail s) == Seq.tail (keys s))
  = Seq.lemma_eq_intro (keys (Seq.tail s)) (Seq.tail (keys s))

let rec lower_bound_keys (#k #v: Type) (c: O.comparer k) (s: Seq.seq (k & v)) (x: k & v)
  : Lemma (ensures S.lower_bound (KC.of_keys k v c) s x == S.lower_bound c (keys s) (fst x))
          (decreases Seq.length s)
  = if Seq.length s = 0 then ()
    else (keys_tail s; lower_bound_keys c (Seq.tail s) x)

/// A search for a pair is a search for its key.
let key_index_keys (#k #v: Type) (c: O.comparer k) (s: Seq.seq (k & v)) (x: k & v)
  : Lemma (S.key_index (KC.of_keys k v c) s x == S.key_index c (keys s) (fst x))
          [SMTPat (S.key_index (KC.of_keys k v c) s x)]
  = lower_bound_keys c s x

/// Pairs are in strict order exactly when their keys are.
let strictly_sorted_keys (#k #v: Type) (c: O.comparer k) (s: Seq.seq (k & v))
  : Lemma (S.strictly_sorted (KC.of_keys k v c) s <==> S.strictly_sorted c (keys s))
          [SMTPat (S.strictly_sorted (KC.of_keys k v c) s)]
  = introduce forall (i j: nat). i < j /\ j < Seq.length s ==>
        (O.compare (KC.of_keys k v c) (Seq.index s i) (Seq.index s j) ==
         O.compare c (Seq.index (keys s) i) (Seq.index (keys s) j))
    with introduce _ ==> _
    with (KC.compare_of_keys #k #v c (Seq.index s i) (Seq.index s j);
             keys_index s i; keys_index s j)
