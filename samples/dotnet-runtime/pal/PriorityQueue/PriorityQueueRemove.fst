module PriorityQueueRemove

/// `PriorityQueue.Remove`'s two proof steps (pal-csharp doc/translation.md §33), on top of
/// `Pulse.Lib.CSharp.Heap`. Removing node `i` of the heap `s[0, n]` puts the last node
/// `x = s[n]` in the hole `i` of `s[0, n)` and sifts it up (if it is below the removed
/// node) or down (otherwise). Every definition here is a definition; nothing is assumed.

module Seq = FStar.Seq
module O = Pulse.Lib.CSharp.Order
module SD = Pulse.Lib.CSharp.Sorted
module S = Pulse.Lib.CSharp.Sort
module H = Pulse.Lib.CSharp.Heap

/// The start: `x` in the hole `i` meets `MoveUp*`'s precondition if it is below `s[i]`,
/// and `MoveDown*`'s otherwise.
let remove_init (e p: Type) (s: Seq.seq (e & p)) (n i: int) (c: O.comparer p)
  : Lemma (requires 0 <= i /\ i < n /\ n < Seq.length s /\
                    H.is_heap e p (Seq.slice s 0 (n + 1)) c)
          (ensures (let x = Seq.index s n in
                    (O.compare (SD.or_default c) (snd x) (snd (Seq.index s i)) < 0 ==>
                       H.up_inv e p s n i x c (Seq.upd (Seq.slice s 0 n) i x)) /\
                    (O.compare (SD.or_default c) (snd x) (snd (Seq.index s i)) >= 0 ==>
                       H.down_inv e p s n i x c (Seq.upd (Seq.slice s 0 n) i x))))
  = reveal_opaque (`%H.up_core) (H.up_core e p);
    reveal_opaque (`%H.down_core) (H.down_core e p);
    let x = Seq.index s n in
    let y = Seq.index s i in
    let r = SD.or_default c in
    let full = Seq.slice s 0 (n + 1) in
    let edge (k: nat)
      : Lemma (requires 0 < k /\ k <= n)
              (ensures H.le c (Seq.index s (H.pi k)) (Seq.index s k))
      = assert (H.le c (Seq.index full (H.pi k)) (Seq.index full k)) in
    introduce forall (k: nat). 0 < k /\ k < n /\ n <= Seq.length s /\ k <> i /\ H.pi k <> i ==>
                               H.le c (Seq.index s (H.pi k)) (Seq.index s k)
    with introduce _ ==> _ with edge k;
    introduce i > 0 ==> H.below c s n i (Seq.index s (H.pi i))
    with begin
      let g = Seq.index s (H.pi i) in
      edge i;
      introduce forall (k: nat). 0 < k /\ k < n /\ n <= Seq.length s /\ H.pi k == i ==>
                                 H.le c g (Seq.index s k)
      with introduce _ ==> _ with
        (edge k; O.compare_trans r (snd g) (snd y) (snd (Seq.index s k)))
    end;
    introduce O.compare r (snd x) (snd y) < 0 ==> H.below c s n i x
    with begin
      introduce forall (k: nat). 0 < k /\ k < n /\ n <= Seq.length s /\ H.pi k == i ==>
                                 H.le c x (Seq.index s k)
      with introduce _ ==> _ with
        (edge k; O.compare_trans r (snd x) (snd y) (snd (Seq.index s k)))
    end;
    introduce O.compare r (snd x) (snd y) >= 0 /\ i > 0 ==> H.le c (Seq.index s (H.pi i)) x
    with (edge i; O.compare_trans r (snd (Seq.index s (H.pi i))) (snd y) (snd x));
    S.permutation_refl (Seq.upd (Seq.slice s 0 n) i x)

/// The end: the old heap `s[0, n]` is the new one with the removed node put back.
let remove_done (e p: Type) (s: Seq.seq (e & p)) (n i: int) (a: Seq.seq (e & p))
  : Lemma (requires 0 <= i /\ i <= n /\ n < Seq.length s /\
                    (i < n ==> S.permutation (Seq.upd (Seq.slice s 0 n) i (Seq.index s n)) a) /\
                    (i == n ==> a == Seq.slice s 0 n))
          (ensures S.permutation (Seq.slice s 0 (n + 1)) (Seq.snoc a (Seq.index s i)))
  = let full = Seq.slice s 0 (n + 1) in
    S.permutation_refl full;
    if i = n then Seq.lemma_eq_intro full (Seq.snoc a (Seq.index s i))
    else begin
      let u = Seq.upd (Seq.slice s 0 n) i (Seq.index s n) in
      S.permutation_swap full full i n;
      Seq.lemma_eq_intro (S.swap full i n) (Seq.snoc u (Seq.index s i));
      H.permutation_snoc u a (Seq.index s i);
      H.permutation_trans full (Seq.snoc u (Seq.index s i)) (Seq.snoc a (Seq.index s i))
    end

module Eq = Pulse.Lib.CSharp.Equality

/// `FindIndex`'s equality: `c`, or the element type's default comparer when `c` is null.
let elem_eq (#e: Type0) (c: option Eq.handle) (x y: e) : bool =
  Eq.equals (match c with | Some h -> h | None -> Eq.default_comparer e) x y

/// No node of `s[0, i)` holds an element equal to `x`.
let no_match (#e #p: Type0) (c: option Eq.handle) (x: e) (s: Seq.seq (e & p)) (i: int) : prop =
  forall (k: nat). k < i /\ k < Seq.length s ==> ~ (elem_eq c x (fst (Seq.index s k)))
