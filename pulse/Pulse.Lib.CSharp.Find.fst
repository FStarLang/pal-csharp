module Pulse.Lib.CSharp.Find

/// The searches, filters and maps that `List<T>`'s delegate-taking members are specified
/// with (doc/translation.md R26.3). Every function is defined here and every lemma proved;
/// the only trusted part is the model of a delegate (`Pulse.Lib.CSharp.Delegate`).

module Seq = FStar.Seq
module D = Pulse.Lib.CSharp.Delegate

/// The first position `k` in `[i, i+n)` with `p s[k] = keep`, or -1. Positions outside `s`
/// never match, so the function is total; its contract is stated for an in-range window.
let rec find_first (#a: Type0) (s: Seq.seq a) (p: D.fn1 a bool) (keep: bool) (i: int) (n: int)
  : Tot int (decreases (if n <= 0 then 0 else n))
  = if n <= 0 then -1
    else if 0 <= i && i < Seq.length s && D.apply1 p (Seq.index s i) = keep then i
    else find_first s p keep (i + 1) (n - 1)

/// The last position `k` in `[lo, lo+n)` with `p s[k] = keep`, or -1.
let rec find_last (#a: Type0) (s: Seq.seq a) (p: D.fn1 a bool) (keep: bool) (lo: int) (n: int)
  : Tot int (decreases (if n <= 0 then 0 else n))
  = if n <= 0 then -1
    else let k = lo + n - 1 in
      if 0 <= k && k < Seq.length s && D.apply1 p (Seq.index s k) = keep then k
      else find_last s p keep lo (n - 1)

let rec find_first_spec (#a: Type0) (s: Seq.seq a) (p: D.fn1 a bool) (keep: bool) (i: int) (n: int)
  : Lemma (requires 0 <= i /\ 0 <= n /\ i + n <= Seq.length s)
          (ensures (let r = find_first s p keep i n in
                    (r == -1 <==> (forall (k: int). i <= k /\ k < i + n ==> D.apply1 p (Seq.index s k) <> keep)) /\
                    (r <> -1 ==> i <= r /\ r < i + n /\ D.apply1 p (Seq.index s r) = keep /\
                                 (forall (k: int). i <= k /\ k < r ==> D.apply1 p (Seq.index s k) <> keep))))
          (decreases n)
          [SMTPat (find_first s p keep i n)]
  = if n = 0 then () else find_first_spec s p keep (i + 1) (n - 1)

let rec find_last_spec (#a: Type0) (s: Seq.seq a) (p: D.fn1 a bool) (keep: bool) (lo: int) (n: int)
  : Lemma (requires 0 <= lo /\ 0 <= n /\ lo + n <= Seq.length s)
          (ensures (let r = find_last s p keep lo n in
                    (r == -1 <==> (forall (k: int). lo <= k /\ k < lo + n ==> D.apply1 p (Seq.index s k) <> keep)) /\
                    (r <> -1 ==> lo <= r /\ r < lo + n /\ D.apply1 p (Seq.index s r) = keep /\
                                 (forall (k: int). r < k /\ k < lo + n ==> D.apply1 p (Seq.index s k) <> keep))))
          (decreases n)
          [SMTPat (find_last s p keep lo n)]
  = if n = 0 then () else find_last_spec s p keep lo (n - 1)

/// `Pal.FindIndex(s, p)` / `Pal.FindIndex(s, p, start, count)`.
let find_index_all (#a: Type0) (s: Seq.seq a) (p: D.fn1 a bool) : int = find_first s p true 0 (Seq.length s)
let find_index (#a: Type0) (s: Seq.seq a) (p: D.fn1 a bool) (start count: int) : int = find_first s p true start count

/// `Pal.FindLastIndex(s, p)` / `Pal.FindLastIndex(s, p, index, count)`, in C#'s
/// `(index, count)` convention: the window is `[index - count + 1, index]`.
let find_last_index_all (#a: Type0) (s: Seq.seq a) (p: D.fn1 a bool) : int = find_last s p true 0 (Seq.length s)
let find_last_index (#a: Type0) (s: Seq.seq a) (p: D.fn1 a bool) (index count: int) : int =
  find_last s p true (index - count + 1) count

/// `Pal.TrueForAll(s, p)`.
let true_for_all (#a: Type0) (s: Seq.seq a) (p: D.fn1 a bool) : bool = find_first s p false 0 (Seq.length s) = -1

/// The elements of the first `n` of `s` with `p x = keep`, in order.
let rec filter_prefix (#a: Type0) (s: Seq.seq a) (p: D.fn1 a bool) (keep: bool) (n: nat { n <= Seq.length s })
  : Tot (Seq.seq a) (decreases n)
  = if n = 0 then Seq.empty
    else let r = filter_prefix s p keep (n - 1) in
      let x = Seq.index s (n - 1) in
      if D.apply1 p x = keep then Seq.snoc r x else r

/// `Pal.FindAll(s, p)` (`keep`) and `Pal.RemoveAll(s, p)` (`not keep`).
let filter (#a: Type0) (s: Seq.seq a) (p: D.fn1 a bool) (keep: bool) : Seq.seq a =
  filter_prefix s p keep (Seq.length s)

unfold let find_all (#a: Type0) (s: Seq.seq a) (p: D.fn1 a bool) : Seq.seq a = filter s p true
unfold let remove_all (#a: Type0) (s: Seq.seq a) (p: D.fn1 a bool) : Seq.seq a = filter s p false

let rec filter_prefix_slice (#a: Type0) (s: Seq.seq a) (p: D.fn1 a bool) (keep: bool)
    (hi: nat { hi <= Seq.length s }) (n: nat { n <= hi })
  : Lemma (ensures filter_prefix (Seq.slice s 0 hi) p keep n == filter_prefix s p keep n)
          (decreases n)
          [SMTPat (filter_prefix (Seq.slice s 0 hi) p keep n)]
  = if n = 0 then () else filter_prefix_slice s p keep hi (n - 1)

let rec filter_prefix_length (#a: Type0) (s: Seq.seq a) (p: D.fn1 a bool) (keep: bool) (n: nat { n <= Seq.length s })
  : Lemma (ensures Seq.length (filter_prefix s p keep n) <= n)
          (decreases n)
          [SMTPat (filter_prefix s p keep n)]
  = if n = 0 then () else filter_prefix_length s p keep (n - 1)

/// A loop that filters in place states its progress as the filter of a prefix; this puts
/// it in the form the recursion unfolds on.
let filter_slice (#a: Type0) (s: Seq.seq a) (p: D.fn1 a bool) (keep: bool) (m: nat { m <= Seq.length s })
  : Lemma (ensures filter (Seq.slice s 0 m) p keep == filter_prefix s p keep m)
          [SMTPat (filter (Seq.slice s 0 m) p keep)]
  = filter_prefix_slice s p keep m m

/// A prefix with no element to drop is kept whole.
let rec filter_prefix_all (#a: Type0) (s: Seq.seq a) (p: D.fn1 a bool) (keep: bool) (n: nat { n <= Seq.length s })
  : Lemma (requires forall (k: nat). k < n ==> D.apply1 p (Seq.index s k) = keep)
          (ensures filter_prefix s p keep n == Seq.slice s 0 n)
          (decreases n)
          [SMTPat (filter_prefix s p keep n)]
  = if n = 0 then Seq.lemma_eq_elim (Seq.slice s 0 0) Seq.empty
    else begin
      filter_prefix_all s p keep (n - 1);
      Seq.lemma_eq_elim (Seq.snoc (Seq.slice s 0 (n - 1)) (Seq.index s (n - 1))) (Seq.slice s 0 n)
    end

/// `Pal.ConvertAll(s, f)`.
let map (#a #b: Type0) (s: Seq.seq a) (f: D.fn1 a b) : Seq.seq b =
  Seq.init (Seq.length s) (fun (i: nat { i < Seq.length s }) -> D.apply1 f (Seq.index s i))

let map_length (#a #b: Type0) (s: Seq.seq a) (f: D.fn1 a b)
  : Lemma (Seq.length (map s f) == Seq.length s) [SMTPat (Seq.length (map s f))]
  = ()

let map_index (#a #b: Type0) (s: Seq.seq a) (f: D.fn1 a b) (i: nat { i < Seq.length s })
  : Lemma (Seq.index (map s f) i == D.apply1 f (Seq.index s i)) [SMTPat (Seq.index (map s f) i)]
  = ()
