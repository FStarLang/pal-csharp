module Pulse.Lib.CSharp.HashChain

/// The separate-chaining hash table that `HashSet<T>` and `Dictionary<TKey,TValue>` share
/// (doc/translation.md §24): an `int[] _buckets` of 1-based chain heads and an `Entry[]
/// _entries` whose `Next` links the chains, with removed entries threaded onto a free list
/// whose links are stored as `StartOfFreeList - next` (`StartOfFreeList = -3`).
///
/// Everything here is proved. The table is described through `ops`, the entry's hash code,
/// link and key, so the one theory serves every entry layout.
///
/// `wfh` is the table invariant with an optional *hole*: an entry that is momentarily
/// neither in a chain nor on the free list, which is what an entry being filled in by an
/// insertion, or just unlinked by a removal, is. `wf` is `wfh` with no hole (`-1`).

open FStar.Seq
module Seq = FStar.Seq
module Eq = Pulse.Lib.CSharp.Equality
module I32 = FStar.Int32

noeq type ops (e: Type0) (k: Type0) = {
  hc  : e -> int;
  nx  : e -> int;
  key : e -> k;
}

/// The bucket of a hash code: `(uint)hashCode % (uint)buckets.Length`.
let bkt (h: int) (len: pos) : nat = (h % 4294967296) % len

/// The code's bucket index, `(int)((uint)h % (uint)len)`, is `bkt`.
let bkt_code (h len: I32.t)
  : Lemma (requires I32.v len > 0)
          (ensures I32.v (FStar.Int.Cast.uint32_to_int32
                            (FStar.UInt32.rem (FStar.Int.Cast.int32_to_uint32 h) (FStar.Int.Cast.int32_to_uint32 len)))
                   == bkt (I32.v h) (I32.v len))
          [SMTPat (FStar.Int.Cast.uint32_to_int32
                     (FStar.UInt32.rem (FStar.Int.Cast.int32_to_uint32 h) (FStar.Int.Cast.int32_to_uint32 len)))]
  = FStar.Math.Lemmas.lemma_mod_lt (I32.v h % 4294967296) (I32.v len)

/// The same index computed as `uint % int`, which C# does in `long`:
/// `(int)((long)h % (long)len)` at a stored `uint` hash code `h`.
let bkt_code_long (h: FStar.UInt32.t) (len: I32.t)
  : Lemma (requires I32.v len > 0)
          (ensures I32.v (FStar.Int.Cast.int64_to_int32
                            (FStar.Int64.rem (FStar.Int.Cast.uint32_to_int64 h) (FStar.Int.Cast.int32_to_int64 len)))
                   == bkt (I32.v (FStar.Int.Cast.uint32_to_int32 h)) (I32.v len))
          [SMTPat (FStar.Int.Cast.int64_to_int32
                     (FStar.Int64.rem (FStar.Int.Cast.uint32_to_int64 h) (FStar.Int.Cast.int32_to_int64 len)))]
  = let u = FStar.UInt32.v h in
    let n = I32.v len in
    FStar.Math.Lemmas.lemma_mod_lt u n;
    FStar.Math.Lemmas.small_mod u 4294967296;
    // (int)h then mod 2^32 is h again
    let x = I32.v (FStar.Int.Cast.uint32_to_int32 h) in
    assert (x % 4294967296 == u % 4294967296);
    assert (FStar.Int64.v (FStar.Int64.rem (FStar.Int.Cast.uint32_to_int64 h) (FStar.Int.Cast.int32_to_int64 len)) == u % n)

let inr (#e: Type0) (es: seq e) (i: int) : bool = 0 <= i && i < Seq.length es

let in_bucket (#e #k: Type0) (o: ops e k) (es: seq e) (b: int) (j: int) : bool =
  inr es j && bkt (o.hc (Seq.index es j)) (Seq.length es) = b

/// The chain successor of any index; out of range is the end of the chain.
let nxt (#e #k: Type0) (o: ops e k) (es: seq e) (i: int) : int =
  if inr es i then o.nx (Seq.index es i) else -1

let rec walk (#e #k: Type0) (o: ops e k) (es: seq e) (i: int) (q: nat)
  : Tot int (decreases q)
  = if q = 0 then i else nxt o es (walk o es i (q - 1))

/// A chain node: live, below the limit `m`, and not the hole.
let lvx (#e #k: Type0) (o: ops e k) (es: seq e) (m hole: int) (j: int) : bool =
  0 <= j && j < m && m <= Seq.length es && j <> hole && o.nx (Seq.index es j) >= -1

let chain_at (#e #k: Type0) (o: ops e k) (es: seq e) (m hole: int) (b: int) (h: int) (l: nat)
  : prop
  = l <= Seq.length es /\
    (forall (q: nat). {:pattern walk o es h q}
       q < l ==> lvx o es m hole (walk o es h q) && in_bucket o es b (walk o es h q)) /\
    walk o es h l == -1 /\
    (forall (q1 q2: nat). {:pattern walk o es h q1; walk o es h q2}
       q1 < q2 /\ q2 < l ==> walk o es h q1 <> walk o es h q2)

let complete_at (#e #k: Type0) (o: ops e k) (es: seq e) (m hole: int) (b: int) (h: int) (l: nat)
  : prop
  = forall (j: int). {:pattern lvx o es m hole j; in_bucket o es b j}
      lvx o es m hole j /\ in_bucket o es b j ==> (exists (q: nat). q < l /\ walk o es h q == j)

let bucket_ok (#e #k: Type0) (o: ops e k) (bs: seq I32.t) (es: seq e) (m hole: int) (b: nat{b < Seq.length bs})
  : prop
  = exists (l: nat). chain_at o es m hole b (I32.v (Seq.index bs b) - 1) l /\
                     complete_at o es m hole b (I32.v (Seq.index bs b) - 1) l

/// `bs'` is `bs` but for bucket `b`.
let same_but (bs bs': seq I32.t) (b: nat) : prop =
  b < Seq.length bs /\ Seq.length bs' == Seq.length bs /\
  (forall (b': nat). {:pattern Seq.index bs' b'} b' < Seq.length bs /\ b' <> b ==> Seq.index bs' b' == Seq.index bs b')

let chains (#e #k: Type0) (o: ops e k) (bs: seq I32.t) (es: seq e) (m hole: int) : prop =
  Seq.length bs == Seq.length es /\
  (forall (b: nat). {:pattern Seq.index bs b} b < Seq.length bs ==> bucket_ok o bs es m hole b)

(* ---------------------------------------------------------------------------------- *)
(* The free list *)

let fnxt (#e #k: Type0) (o: ops e k) (es: seq e) (i: int) : int =
  if inr es i then -3 - o.nx (Seq.index es i) else -1

let rec fwalk (#e #k: Type0) (o: ops e k) (es: seq e) (i: int) (q: nat)
  : Tot int (decreases q)
  = if q = 0 then i else fnxt o es (fwalk o es i (q - 1))

let dead (#e #k: Type0) (o: ops e k) (es: seq e) (n hole: int) (j: int) : bool =
  0 <= j && j < n && n <= Seq.length es && j <> hole && o.nx (Seq.index es j) < -1

let rec ndead (#e #k: Type0) (o: ops e k) (es: seq e) (n: nat{n <= Seq.length es}) (hole: int)
  : Tot nat (decreases n)
  = if n = 0 then 0
    else ndead o es (n - 1) hole +
         (if n - 1 <> hole && o.nx (Seq.index es (n - 1)) < -1 then 1 else 0)

/// The live keys, in index order: what the collection holds.
let rec items (#e #k: Type0) (o: ops e k) (es: seq e) (n: nat{n <= Seq.length es}) (hole: int)
  : Tot (seq k) (decreases n)
  = if n = 0 then Seq.empty
    else let r = items o es (n - 1) hole in
         if n - 1 <> hole && o.nx (Seq.index es (n - 1)) >= -1
         then Seq.snoc r (o.key (Seq.index es (n - 1)))
         else r

let free_ok (#e #k: Type0) (o: ops e k) (es: seq e) (n hole fl fc: int) : prop =
  0 <= n /\ n <= Seq.length es /\ 0 <= fc /\
  (forall (q: nat). {:pattern fwalk o es fl q} q < fc ==> dead o es n hole (fwalk o es fl q)) /\
  fwalk o es fl fc == -1 /\
  (forall (q1 q2: nat). {:pattern fwalk o es fl q1; fwalk o es fl q2}
     q1 < q2 /\ q2 < fc ==> fwalk o es fl q1 <> fwalk o es fl q2) /\
  ndead o es n hole == fc

(* ---------------------------------------------------------------------------------- *)
(* Hash codes *)

/// The hash a table stores for a key, at the comparer `c`.
let hv (#k: Type0) (c: Eq.handle) (x: k) : int = I32.v (Eq.hash c x)

let hashes_ok (#e #k: Type0) (o: ops e k) (c: Eq.handle) (es: seq e) (n hole: int) : prop =
  forall (j: int). {:pattern lvx o es n hole j}
    lvx o es n hole j ==> o.hc (Seq.index es j) == hv c (o.key (Seq.index es j))

(* ---------------------------------------------------------------------------------- *)
(* The invariant *)

let wfh (#e #k: Type0) (o: ops e k) (c: Eq.handle) (bs: seq I32.t) (es: seq e)
        (n hole fl fc: int)
  : prop
  = 0 <= n /\ n <= Seq.length es /\
    (hole == -1 \/ (0 <= hole /\ hole < n)) /\
    chains o bs es n hole /\
    free_ok o es n hole fl fc /\
    hashes_ok o c es n hole

let wf (#e #k: Type0) (o: ops e k) (c: Eq.handle) (bs: seq I32.t) (es: seq e) (n fl fc: int)
  : prop
  = wfh o c bs es n (-1) fl fc

/// `∃ p. c.Equals(xs[p], x)`: what `Contains(x)` answers.
let mem (#k: Type0) (c: Eq.handle) (xs: seq k) (x: k) : prop =
  exists (p: nat). p < Seq.length xs /\ Eq.equals c (Seq.index xs p) x

(* ---------------------------------------------------------------------------------- *)
(* Walks *)

let rec walk_shift (#e #k: Type0) (o: ops e k) (es: seq e) (i: int) (q: nat)
  : Lemma (ensures walk o es (nxt o es i) q == walk o es i (q + 1)) (decreases q)
  = if q = 0 then () else walk_shift o es i (q - 1)

let rec walk_frame (#e #k: Type0) (o: ops e k) (es es': seq e) (h: int) (q: nat)
  : Lemma (requires forall (q': nat). q' < q ==> nxt o es (walk o es h q') == nxt o es' (walk o es h q'))
          (ensures walk o es' h q == walk o es h q)
          (decreases q)
  = if q = 0 then () else walk_frame o es es' h (q - 1)

let rec walk_end (#e #k: Type0) (o: ops e k) (es: seq e) (h: int) (l: nat) (q: nat)
  : Lemma (requires walk o es h l == -1 /\ q >= l) (ensures walk o es h q == -1) (decreases q)
  = if q = l then () else walk_end o es h l (q - 1)

/// The length of a chain is determined by its start.
let chain_len_unique (#e #k: Type0) (o: ops e k) (es: seq e) (m hole b h: int) (l1 l2: nat)
  : Lemma (requires chain_at o es m hole b h l1 /\ chain_at o es m hole b h l2) (ensures l1 == l2)
  = if l1 < l2 then (assert (lvx o es m hole (walk o es h l1)))
    else if l2 < l1 then (assert (lvx o es m hole (walk o es h l2)))
    else ()

(* ---------------------------------------------------------------------------------- *)
(* Searching a chain (FindItemIndex, and the search phase of Remove and Add) *)

/// `c.Equals(e.Key, x)` and the stored hash code is `h`: what a search stops at.
let hit (#e #k: Type0) (o: ops e k) (c: Eq.handle) (es: seq e) (h: int) (x: k) (j: int) : bool =
  inr es j && o.hc (Seq.index es j) = h && Eq.equals c (o.key (Seq.index es j)) x

/// The search for `x`, whose hash is `h`, has followed `q` links of its bucket's chain to
/// `i`, and none of the entries passed is a hit.
let search (#e #k: Type0) (o: ops e k) (c: Eq.handle) (bs: seq I32.t) (es: seq e)
           (n fl fc: int) (x: k) (i: int) (q: nat)
  : prop
  = wf o c bs es n fl fc /\ Seq.length es > 0 /\
    (let b = bkt (hv c x) (Seq.length es) in
     i == walk o es (I32.v (Seq.index bs b) - 1) q /\
     (forall (q': nat). {:pattern walk o es (I32.v (Seq.index bs b) - 1) q'}
        q' < q ==> not (hit o c es (hv c x) x (walk o es (I32.v (Seq.index bs b) - 1) q'))))


let chain_of (#e #k: Type0) (o: ops e k) (c: Eq.handle) (bs: seq I32.t) (es: seq e)
             (n fl fc: int) (b: nat)
  : Ghost nat (requires wf o c bs es n fl fc /\ b < Seq.length bs)
              (ensures fun l -> chain_at o es n (-1) b (I32.v (Seq.index bs b) - 1) l /\
                               complete_at o es n (-1) b (I32.v (Seq.index bs b) - 1) l)
  = assert (bucket_ok o bs es n (-1) b);
    FStar.IndefiniteDescription.indefinite_description_ghost nat
      (fun l -> chain_at o es n (-1) b (I32.v (Seq.index bs b) - 1) l /\
                complete_at o es n (-1) b (I32.v (Seq.index bs b) - 1) l)

let search_start (#e #k: Type0) (o: ops e k) (c: Eq.handle) (bs: seq I32.t) (es: seq e)
                 (n fl fc: int) (x: k)
  : Lemma (requires wf o c bs es n fl fc /\ Seq.length es > 0)
          (ensures search o c bs es n fl fc x (I32.v (Seq.index bs (bkt (hv c x) (Seq.length es))) - 1) 0 /\
                   0 <= I32.v (Seq.index bs (bkt (hv c x) (Seq.length es))) /\
                   I32.v (Seq.index bs (bkt (hv c x) (Seq.length es))) <= Seq.length es)
  = let b = bkt (hv c x) (Seq.length es) in
    let l = chain_of o c bs es n fl fc b in
    let h = I32.v (Seq.index bs b) - 1 in
    if l = 0 then assert (walk o es h 0 == h) else assert (lvx o es n (-1) (walk o es h 0))

/// A step past an entry that is not a hit: the search goes on, and has followed no more
/// links than the table has entries -- so `collisionCount` never exceeds the length.
let search_step (#e #k: Type0) (o: ops e k) (c: Eq.handle) (bs: seq I32.t) (es: seq e)
                (n fl fc: int) (x: k) (i: int) (q: nat)
  : Lemma (requires search o c bs es n fl fc x i q /\ inr es i /\ not (hit o c es (hv c x) x i))
          (ensures search o c bs es n fl fc x (o.nx (Seq.index es i)) (q + 1) /\
                   q + 1 <= Seq.length es)
  = let b = bkt (hv c x) (Seq.length es) in
    let h = I32.v (Seq.index bs b) - 1 in
    let l = chain_of o c bs es n fl fc b in
    if q >= l then walk_end o es h l q;
    assert (walk o es h (q + 1) == nxt o es i)

/// A search that stops at an entry in range has found a live entry equal to `x`.
let search_found (#e #k: Type0) (o: ops e k) (c: Eq.handle) (bs: seq I32.t) (es: seq e)
                 (n fl fc: int) (x: k) (i: int) (q: nat)
  : Lemma (requires search o c bs es n fl fc x i q /\ inr es i)
          (ensures lvx o es n (-1) i /\ q < Seq.length es)
  = let b = bkt (hv c x) (Seq.length es) in
    let h = I32.v (Seq.index bs b) - 1 in
    let l = chain_of o c bs es n fl fc b in
    if q >= l then walk_end o es h l q

/// A search that runs off its chain has passed every live entry equal to `x`.
let search_none (#e #k: Type0) (o: ops e k) (c: Eq.handle) (bs: seq I32.t) (es: seq e)
                (n fl fc: int) (x: k) (i: int) (q: nat) (j: int)
  : Lemma (requires search o c bs es n fl fc x i q /\ not (inr es i) /\ lvx o es n (-1) j)
          (ensures not (Eq.equals c (o.key (Seq.index es j)) x))
  = let b = bkt (hv c x) (Seq.length es) in
    let h = I32.v (Seq.index bs b) - 1 in
    let l = chain_of o c bs es n fl fc b in
    if Eq.equals c (o.key (Seq.index es j)) x then begin
      Eq.equals_hash c (o.key (Seq.index es j)) x;
      assert (in_bucket o es b j);
      let aux (q': nat) : Lemma (requires q' < l /\ walk o es h q' == j) (ensures False) =
        if q' < q then () else (assert (lvx o es n (-1) (walk o es h q)))
      in
      FStar.Classical.forall_intro (FStar.Classical.move_requires aux)
    end

(* ---------------------------------------------------------------------------------- *)
(* Sequences *)

let remove_at (#a: Type) (s: seq a) (p: nat{p < Seq.length s}) : seq a =
  Seq.append (Seq.slice s 0 p) (Seq.slice s (p + 1) (Seq.length s))

let insert_at (#a: Type) (s: seq a) (p: nat{p <= Seq.length s}) (x: a) : seq a =
  Seq.append (Seq.slice s 0 p) (Seq.cons x (Seq.slice s p (Seq.length s)))

let insert_at_length (#a: Type) (s: seq a) (p: nat{p <= Seq.length s}) (x: a)
  : Lemma (Seq.length (insert_at s p x) == Seq.length s + 1 /\ Seq.index (insert_at s p x) p == x)
          [SMTPat (insert_at s p x)]
  = ()

let insert_at_end (#a: Type) (s: seq a) (x: a)
  : Lemma (insert_at s (Seq.length s) x == Seq.snoc s x)
  = assert (Seq.equal (insert_at s (Seq.length s) x) (Seq.snoc s x))

let insert_snoc (#a: Type) (s: seq a) (p: nat{p <= Seq.length s}) (x y: a)
  : Lemma (Seq.snoc (insert_at s p x) y == insert_at (Seq.snoc s y) p x)
  = assert (Seq.equal (Seq.snoc (insert_at s p x) y) (insert_at (Seq.snoc s y) p x))

let remove_insert (#a: Type) (s: seq a) (p: nat{p <= Seq.length s}) (x: a)
  : Lemma (remove_at (insert_at s p x) p == s)
  = assert (Seq.equal (remove_at (insert_at s p x) p) s)

(* ---------------------------------------------------------------------------------- *)
(* Items and the dead count *)

let rec items_frame (#e #k: Type0) (o: ops e k) (es es': seq e) (n: nat) (hole: int)
  : Lemma (requires n <= Seq.length es /\ n <= Seq.length es' /\
                    (forall (j: nat). j < n /\ j <> hole ==>
                       (o.nx (Seq.index es j) >= -1) == (o.nx (Seq.index es' j) >= -1) /\
                       (o.nx (Seq.index es j) >= -1 ==> o.key (Seq.index es j) == o.key (Seq.index es' j))))
          (ensures items o es n hole == items o es' n hole /\ ndead o es n hole == ndead o es' n hole)
          (decreases n)
  = if n = 0 then () else items_frame o es es' (n - 1) hole

let rec items_below (#e #k: Type0) (o: ops e k) (es: seq e) (n: nat{n <= Seq.length es}) (hole: int)
  : Lemma (requires n <= hole)
          (ensures items o es n hole == items o es n (-1) /\ ndead o es n hole == ndead o es n (-1))
          (decreases n)
  = if n = 0 then () else items_below o es (n - 1) hole

let rec count_items (#e #k: Type0) (o: ops e k) (es: seq e) (n: nat{n <= Seq.length es}) (hole: int)
  : Lemma (ensures Seq.length (items o es n hole) + ndead o es n hole +
                   (if 0 <= hole && hole < n then 1 else 0) == n)
          (decreases n)
  = if n = 0 then () else count_items o es (n - 1) hole

/// Where the entry `j` sits among the items: the live entries before it.
let pos (#e #k: Type0) (o: ops e k) (es: seq e) (j: nat{j <= Seq.length es}) : nat =
  Seq.length (items o es j (-1))

let rec items_hole (#e #k: Type0) (o: ops e k) (es: seq e) (n: nat{n <= Seq.length es}) (h: nat{h < n})
  : Lemma (ensures (let s = items o es n h in
                    pos o es h <= Seq.length s /\
                    (if o.nx (Seq.index es h) >= -1
                     then items o es n (-1) == insert_at s (pos o es h) (o.key (Seq.index es h)) /\
                          ndead o es n (-1) == ndead o es n h
                     else items o es n (-1) == s /\ ndead o es n (-1) == ndead o es n h + 1)))
          (decreases n)
  = if n = h + 1 then begin
      items_below o es h h;
      insert_at_end (items o es h (-1)) (o.key (Seq.index es h))
    end else begin
      items_hole o es (n - 1) h;
      if o.nx (Seq.index es h) >= -1 && o.nx (Seq.index es (n - 1)) >= -1 then
        insert_snoc (items o es (n - 1) h) (pos o es h) (o.key (Seq.index es h))
                    (o.key (Seq.index es (n - 1)))
    end

let rec items_index (#e #k: Type0) (o: ops e k) (es: seq e) (n: nat{n <= Seq.length es}) (j: nat)
  : Lemma (requires j < n /\ o.nx (Seq.index es j) >= -1)
          (ensures pos o es j < Seq.length (items o es n (-1)) /\
                   Seq.index (items o es n (-1)) (pos o es j) == o.key (Seq.index es j))
          (decreases n)
  = if n = j + 1 then () else items_index o es (n - 1) j

let rec items_live (#e #k: Type0) (o: ops e k) (es: seq e) (n: nat{n <= Seq.length es}) (p: nat)
  : Ghost nat (requires p < Seq.length (items o es n (-1)))
              (ensures fun j -> j < n /\ o.nx (Seq.index es j) >= -1 /\
                               Seq.index (items o es n (-1)) p == o.key (Seq.index es j))
              (decreases n)
  = if p < Seq.length (items o es (n - 1) (-1)) then items_live o es (n - 1) p else n - 1

(* ---------------------------------------------------------------------------------- *)
(* Walk bounds *)

let distinct_bound (#e #k: Type0) (o: ops e k) (es: seq e) (h: int) (l: nat)
  : Lemma (requires (forall (q: nat). q < l ==> inr es (walk o es h q)) /\
                    (forall (q1 q2: nat). q1 < q2 /\ q2 < l ==> walk o es h q1 <> walk o es h q2))
          (ensures l <= Seq.length es)
  = if l > Seq.length es then begin
      let len = Seq.length es in
      let f (q: nat{q < l}) : FStar.Fin.under len = walk o es h q in
      let s : seq (FStar.Fin.under len) = Seq.init l f in
      let (i1, i2) = FStar.Fin.pigeonhole #len s in
      assert (Seq.index s i1 == walk o es h i1);
      assert (Seq.index s i2 == walk o es h i2)
    end

let rec fwalk_shift (#e #k: Type0) (o: ops e k) (es: seq e) (i: int) (q: nat)
  : Lemma (ensures fwalk o es (fnxt o es i) q == fwalk o es i (q + 1)) (decreases q)
  = if q = 0 then () else fwalk_shift o es i (q - 1)

let rec fwalk_frame (#e #k: Type0) (o: ops e k) (es es': seq e) (h: int) (q: nat)
  : Lemma (requires forall (q': nat). q' < q ==> fnxt o es (fwalk o es h q') == fnxt o es' (fwalk o es h q'))
          (ensures fwalk o es' h q == fwalk o es h q)
          (decreases q)
  = if q = 0 then () else fwalk_frame o es es' h (q - 1)

(* ---------------------------------------------------------------------------------- *)
(* The free list under change *)

/// The free list survives any change that keeps the dead entries, and their links.
let free_same (#e #k: Type0) (o: ops e k) (es es': seq e) (n hole hole' fl fc: int)
  : Lemma (requires free_ok o es n hole fl fc /\ Seq.length es' == Seq.length es /\
                    (forall (j: int). dead o es n hole j == dead o es' n hole' j) /\
                    (forall (j: int). dead o es n hole j ==> o.nx (Seq.index es' j) == o.nx (Seq.index es j)) /\
                    ndead o es' n hole' == ndead o es n hole)
          (ensures free_ok o es' n hole' fl fc)
  = let aux (q: nat) : Lemma (fwalk o es' fl q == fwalk o es fl q) =
      if q <= fc then fwalk_frame o es es' fl q
      else begin
        fwalk_frame o es es' fl fc;
        let rec beyond (r: nat) : Lemma (requires r >= fc)
                                         (ensures fwalk o es' fl r == -1 /\ fwalk o es fl r == -1)
                                         (decreases r)
          = if r = fc then () else beyond (r - 1)
        in beyond q
      end
    in
    FStar.Classical.forall_intro aux

let fl_range (#e #k: Type0) (o: ops e k) (es: seq e) (n hole fl fc: int)
  : Lemma (requires free_ok o es n hole fl fc)
          (ensures fl >= -1 /\ (fc > 0 ==> dead o es n hole fl) /\ (fc == 0 ==> fl == -1))
  = assert (fwalk o es fl 0 == fl)

/// `entries[h].Next = StartOfFreeList - _freeList; _freeList = h; _freeCount++`.
let free_push (#e #k: Type0) (o: ops e k) (es: seq e) (n h fl fc: int)
  : Lemma (requires free_ok o es n h fl fc /\ 0 <= h /\ h < n /\ o.nx (Seq.index es h) == -3 - fl)
          (ensures free_ok o es n (-1) h (fc + 1))
  = fl_range o es n h fl fc;
    items_hole o es n h;
    let aux (q: nat) : Lemma (fwalk o es h (q + 1) == fwalk o es fl q) = fwalk_shift o es h q in
    FStar.Classical.forall_intro aux;
    assert (fwalk o es h (fc + 1) == fwalk o es fl fc);
    let d (q1 q2: nat) : Lemma (requires q1 < q2 /\ q2 < fc + 1)
                               (ensures fwalk o es h q1 <> fwalk o es h q2) =
      if q1 = 0 then assert (dead o es n h (fwalk o es fl (q2 - 1)))
      else assert (fwalk o es h q1 == fwalk o es fl (q1 - 1))
    in
    FStar.Classical.forall_intro_2 (fun q1 q2 -> FStar.Classical.move_requires (d q1) q2);
    let dd (q: nat) : Lemma (requires q < fc + 1) (ensures dead o es n (-1) (fwalk o es h q)) =
      if q = 0 then () else assert (dead o es n h (fwalk o es fl (q - 1)))
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires dd)

/// `index = _freeList; _freeCount--; _freeList = StartOfFreeList - entries[_freeList].Next`.
let free_pop (#e #k: Type0) (o: ops e k) (es: seq e) (n fl fc: int)
  : Lemma (requires free_ok o es n (-1) fl fc /\ fc > 0)
          (ensures dead o es n (-1) fl /\ fnxt o es fl >= -1 /\
                   free_ok o es n fl (fnxt o es fl) (fc - 1))
  = fl_range o es n (-1) fl fc;
    items_hole o es n fl;
    let aux (q: nat) : Lemma (fwalk o es (fnxt o es fl) q == fwalk o es fl (q + 1)) = fwalk_shift o es fl q in
    FStar.Classical.forall_intro aux;
    let dd (q: nat) : Lemma (requires q < fc - 1) (ensures dead o es n fl (fwalk o es fl (q + 1))) =
      assert (fwalk o es fl 0 <> fwalk o es fl (q + 1))
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires dd);
    if fc > 1 then assert (dead o es n (-1) (fwalk o es fl 1))

(* ---------------------------------------------------------------------------------- *)
(* Chains under change *)

/// The chains survive any change that keeps the set of chain nodes, and their links and
/// hash codes.
let chains_same (#e #k: Type0) (o: ops e k) (bs: seq I32.t) (es es': seq e) (m hole m' hole': int)
  : Lemma (requires chains o bs es m hole /\ Seq.length es' == Seq.length es /\
                    (forall (j: int). lvx o es m hole j == lvx o es' m' hole' j) /\
                    (forall (j: int). lvx o es m hole j ==>
                       o.nx (Seq.index es' j) == o.nx (Seq.index es j) /\
                       o.hc (Seq.index es' j) == o.hc (Seq.index es j)))
          (ensures chains o bs es' m' hole')
  = let one (b: nat) : Lemma (b < Seq.length bs ==> bucket_ok o bs es' m' hole' b) =
      if b < Seq.length bs then begin
      let h = I32.v (Seq.index bs b) - 1 in
      let l = FStar.IndefiniteDescription.indefinite_description_ghost nat
                (fun l -> chain_at o es m hole b h l /\ complete_at o es m hole b h l) in
      let w (q: nat) : Lemma (requires q <= l) (ensures walk o es' h q == walk o es h q) =
        walk_frame o es es' h q
      in
      FStar.Classical.forall_intro (FStar.Classical.move_requires w);
      assert (chain_at o es' m' hole' b h l);
      let c (j: int) : Lemma (requires lvx o es' m' hole' j /\ in_bucket o es' b j)
                             (ensures exists (q: nat). q < l /\ walk o es' h q == j) =
        assert (lvx o es m hole j /\ in_bucket o es b j)
      in
      FStar.Classical.forall_intro (FStar.Classical.move_requires c);
      assert (complete_at o es' m' hole' b h l)
      end
    in
    FStar.Classical.forall_intro one

/// One bucket's chain survives a change that keeps its nodes, their links and hash codes,
/// and adds no node to the bucket.
let bucket_frame (#e #k: Type0) (o: ops e k) (bs bs': seq I32.t) (es es': seq e)
                 (m hole m' hole': int) (b: nat)
  : Lemma (requires b < Seq.length bs /\ bucket_ok o bs es m hole b /\
                    Seq.length es' == Seq.length es /\ Seq.length bs' == Seq.length bs /\
                    Seq.index bs' b == Seq.index bs b /\
                    (forall (j: int). lvx o es m hole j /\ in_bucket o es b j ==>
                       lvx o es' m' hole' j /\
                       o.nx (Seq.index es' j) == o.nx (Seq.index es j) /\
                       o.hc (Seq.index es' j) == o.hc (Seq.index es j)) /\
                    (forall (j: int). lvx o es' m' hole' j /\ in_bucket o es' b j ==>
                       lvx o es m hole j /\ in_bucket o es b j))
          (ensures bucket_ok o bs' es' m' hole' b)
  = let h = I32.v (Seq.index bs b) - 1 in
    let l = FStar.IndefiniteDescription.indefinite_description_ghost nat
              (fun l -> chain_at o es m hole b h l /\ complete_at o es m hole b h l) in
    let w (q: nat) : Lemma (requires q <= l) (ensures walk o es' h q == walk o es h q) =
      walk_frame o es es' h q
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires w);
    assert (chain_at o es' m' hole' b h l);
    let c (j: int) : Lemma (requires lvx o es' m' hole' j /\ in_bucket o es' b j)
                           (ensures exists (q: nat). q < l /\ walk o es' h q == j) = ()
    in
    FStar.Classical.forall_intro (FStar.Classical.move_requires c);
    assert (complete_at o es' m' hole' b h l)

/// Linking the entry `x` in at the head of its bucket's chain.
let chain_distinct (#e #k: Type0) (o: ops e k) (es: seq e) (m hole b h: int) (l: nat) (q1 q2: nat)
  : Lemma (requires chain_at o es m hole b h l /\ q1 < q2 /\ q2 < l)
          (ensures walk o es h q1 <> walk o es h q2)
  = ()

let chain_live (#e #k: Type0) (o: ops e k) (es: seq e) (m hole b h: int) (l: nat) (q: nat)
  : Lemma (requires chain_at o es m hole b h l /\ q < l)
          (ensures lvx o es m hole (walk o es h q) /\ in_bucket o es b (walk o es h q))
  = ()

let chains_link (#e #k: Type0) (o: ops e k) (bs bs': seq I32.t) (es es': seq e)
                (m hole m' hole': int) (x: int)
  : Lemma (requires chains o bs es m hole /\ Seq.length es' == Seq.length es /\ inr es x /\
                    not (lvx o es m hole x) /\
                    (forall (j: int). lvx o es' m' hole' j == (lvx o es m hole j || j = x)) /\
                    (forall (j: int). lvx o es m hole j ==>
                       o.nx (Seq.index es' j) == o.nx (Seq.index es j) /\
                       o.hc (Seq.index es' j) == o.hc (Seq.index es j)) /\
                    (let b = bkt (o.hc (Seq.index es' x)) (Seq.length es) in
                     o.nx (Seq.index es' x) == I32.v (Seq.index bs b) - 1 /\ same_but bs bs' b /\ I32.v (Seq.index bs' b) == x + 1))
          (ensures chains o bs' es' m' hole')
  = let len = Seq.length es in
    let bx = bkt (o.hc (Seq.index es' x)) len in
    let one (b: nat) : Lemma (b < Seq.length bs' ==> bucket_ok o bs' es' m' hole' b) =
      if b < Seq.length bs' then begin
        if b <> bx then bucket_frame o bs bs' es es' m hole m' hole' b
        else begin
          let h = I32.v (Seq.index bs b) - 1 in
          let l = FStar.IndefiniteDescription.indefinite_description_ghost nat
                    (fun l -> chain_at o es m hole b h l /\ complete_at o es m hole b h l) in
          let w (q: nat) : Lemma (walk o es' x (q + 1) == walk o es h q) =
            walk_shift o es' x q;
            let fr (q': nat) : Lemma (nxt o es (walk o es h q') == nxt o es' (walk o es h q')) =
              if q' >= l then walk_end o es h l q'
            in
            FStar.Classical.forall_intro fr;
            walk_frame o es es' h q
          in
          let d (q1 q2: nat) : Lemma (requires q1 < q2 /\ q2 < l + 1)
                                     (ensures walk o es' x q1 <> walk o es' x q2) =
            let r2 = q2 - 1 in
            w r2;
            assert (walk o es' x q2 == walk o es h r2);
            if q1 > 0 then begin
              let r1 = q1 - 1 in
              w r1;
              assert (walk o es' x q1 == walk o es h r1);
              chain_distinct o es m hole b h l r1 r2
            end else begin
              chain_live o es m hole b h l r2;
              assert (walk o es' x q1 == x)
            end
          in
          FStar.Classical.forall_intro_2 (fun q1 q2 -> FStar.Classical.move_requires (d q1) q2);
          let lv (q: nat) : Lemma (requires q < l + 1)
                                  (ensures lvx o es' m' hole' (walk o es' x q) &&
                                           in_bucket o es' b (walk o es' x q)) =
            if q = 0 then () else begin
              w (q - 1);
              let j = walk o es h (q - 1) in
              assert (chain_at o es m hole b h l);
              assert (lvx o es m hole j);
              assert (in_bucket o es b j);
              assert (lvx o es' m' hole' j);
              assert (in_bucket o es' b j)
            end
          in
          FStar.Classical.forall_intro (FStar.Classical.move_requires lv);
          let ir (q: nat) : Lemma (requires q < l + 1) (ensures inr es' (walk o es' x q)) = lv q in
          FStar.Classical.forall_intro (FStar.Classical.move_requires ir);
          distinct_bound o es' x (l + 1);
          w l;
          assert (I32.v (Seq.index bs' b) - 1 == x);
          assert (chain_at o es' m' hole' b x (l + 1));
          let c (j: int) : Lemma (requires lvx o es' m' hole' j /\ in_bucket o es' b j)
                                 (ensures exists (q: nat). q < l + 1 /\ walk o es' x q == j) =
            if j = x then assert (walk o es' x 0 == x)
            else begin
              assert (lvx o es m hole j /\ in_bucket o es b j);
              let q = FStar.IndefiniteDescription.indefinite_description_ghost nat
                        (fun q -> q < l /\ walk o es h q == j) in
              w q;
              assert (q + 1 < l + 1 /\ walk o es' x (q + 1) == j)
            end
          in
          FStar.Classical.forall_intro (FStar.Classical.move_requires c);
          assert (complete_at o es' m' hole' b x (l + 1))
        end
      end
    in
    FStar.Classical.forall_intro one

(* ---------------------------------------------------------------------------------- *)
(* The collection's view *)

let items_zero (#e #k: Type0) (o: ops e k) (es: seq e) (n: nat{n <= Seq.length es}) (hole: int)
  : Lemma (requires n == 0) (ensures items o es n hole == Seq.empty /\ ndead o es n hole == 0)
  = ()

/// `Array.Clear(buckets); _count = 0; _freeList = -1; _freeCount = 0`, or a fresh table.
let wf_empty (#e #k: Type0) (o: ops e k) (c: Eq.handle) (bs: seq I32.t) (es: seq e)
  : Lemma (requires Seq.length bs == Seq.length es /\
                    (forall (b: nat). b < Seq.length bs ==> I32.v (Seq.index bs b) == 0))
          (ensures wf o c bs es 0 (-1) 0 /\ items o es 0 (-1) == Seq.empty)
  = let one (b: nat) : Lemma (b < Seq.length bs ==> bucket_ok o bs es 0 (-1) b) =
      if b < Seq.length bs then assert (chain_at o es 0 (-1) b (-1) 0 /\ complete_at o es 0 (-1) b (-1) 0)
    in
    FStar.Classical.forall_intro one

/// The table holds `n - fc` items.
let wf_count (#e #k: Type0) (o: ops e k) (c: Eq.handle) (bs: seq I32.t) (es: seq e) (n fl fc: int)
  : Lemma (requires wf o c bs es n fl fc)
          (ensures Seq.length (items o es n (-1)) == n - fc)
  = count_items o es n (-1)

/// The items are the keys of the chain nodes.
let mem_live (#e #k: Type0) (o: ops e k) (c: Eq.handle) (es: seq e) (n: nat{n <= Seq.length es}) (x: k)
  : Lemma (requires mem c (items o es n (-1)) x)
          (ensures exists (j: int). lvx o es n (-1) j /\ Eq.equals c (o.key (Seq.index es j)) x)
  = let p = FStar.IndefiniteDescription.indefinite_description_ghost nat
              (fun p -> p < Seq.length (items o es n (-1)) /\ Eq.equals c (Seq.index (items o es n (-1)) p) x) in
    let j = items_live o es n p in
    assert (lvx o es n (-1) j)

let live_mem (#e #k: Type0) (o: ops e k) (c: Eq.handle) (es: seq e) (n: nat{n <= Seq.length es}) (x: k) (j: int)
  : Lemma (requires lvx o es n (-1) j /\ Eq.equals c (o.key (Seq.index es j)) x)
          (ensures mem c (items o es n (-1)) x /\ pos o es j < Seq.length (items o es n (-1)) /\
                   Seq.index (items o es n (-1)) (pos o es j) == o.key (Seq.index es j))
  = items_index o es n j

/// `FindItemIndex` ran off its chain: `x` is not in the table.
let search_absent (#e #k: Type0) (o: ops e k) (c: Eq.handle) (bs: seq I32.t) (es: seq e)
                  (n fl fc: int) (x: k) (i: int) (q: nat)
  : Lemma (requires search o c bs es n fl fc x i q /\ not (inr es i))
          (ensures ~ (mem c (items o es n (-1)) x))
  = let aux () : Lemma (requires mem c (items o es n (-1)) x) (ensures False) =
      mem_live o c es n x;
      let j = FStar.IndefiniteDescription.indefinite_description_ghost int
                (fun j -> lvx o es n (-1) j /\ Eq.equals c (o.key (Seq.index es j)) x) in
      search_none o c bs es n fl fc x i q j
    in
    FStar.Classical.move_requires aux ()

/// `FindItemIndex` stopped at a hit: `x` is in the table, at the live entry `i`.
let search_hit (#e #k: Type0) (o: ops e k) (c: Eq.handle) (bs: seq I32.t) (es: seq e)
               (n fl fc: int) (x: k) (i: int) (q: nat)
  : Lemma (requires search o c bs es n fl fc x i q /\ hit o c es (hv c x) x i)
          (ensures lvx o es n (-1) i /\ mem c (items o es n (-1)) x)
  = search_found o c bs es n fl fc x i q;
    live_mem o c es n x i

(* ---------------------------------------------------------------------------------- *)
(* Unlinking (Remove) *)

let skip (q r: nat) : nat = if r < q then r else r + 1

/// The predecessor of the `q`th node of the chain from `h`, if it has one.
let prev (#e #k: Type0) (o: ops e k) (es: seq e) (h: int) (q: nat) : int =
  if q = 0 then -2 else walk o es h (q - 1)

let rec unlink_walk (#e #k: Type0) (o: ops e k) (es es': seq e) (m: int) (b h: int) (l q: nat) (x h': int) (r: nat)
  : Lemma (requires chain_at o es m (-1) b h l /\ q < l /\ x == walk o es h q /\ r <= l - 1 /\
                    Seq.length es' == Seq.length es /\
                    h' == (if q = 0 then walk o es h 1 else h) /\
                    (forall (j: int). lvx o es m (-1) j /\ j <> x /\ (j <> prev o es h q \/ q = 0) ==>
                       o.nx (Seq.index es' j) == o.nx (Seq.index es j)) /\
                    (q > 0 ==> o.nx (Seq.index es' (prev o es h q)) == o.nx (Seq.index es x)))
          (ensures walk o es' h' r == walk o es h (skip q r))
          (decreases r)
  = if r = 0 then () else begin
      unlink_walk o es es' m b h l q x h' (r - 1);
      let r0 = skip q (r - 1) in
      let j = walk o es h r0 in
      chain_live o es m (-1) b h l r0;
      if r0 <> q then chain_distinct o es m (-1) b h l (if r0 < q then r0 else q) (if r0 < q then q else r0);
      assert (walk o es' h' r == nxt o es' j);
      if q > 0 && r - 1 = q - 1 then begin
        assert (walk o es h (q + 1) == nxt o es x)
      end else begin
        assert (skip q r == r0 + 1);
        if q > 0 && r0 = q - 1 then () else
        if q > 0 then chain_distinct o es m (-1) b h l (if r0 < q - 1 then r0 else q - 1) (if r0 < q - 1 then q - 1 else r0);
        assert (nxt o es' j == nxt o es j)
      end
    end

/// Unlinking the `q`th node `x` of bucket `b`'s chain, either by moving the bucket's head
/// past it (`q = 0`) or by linking its predecessor past it, leaves `x` as the hole.
let chains_unlink (#e #k: Type0) (o: ops e k) (bs bs': seq I32.t) (es es': seq e)
                  (m: int) (b: nat) (l q: nat) (x: int)
  : Lemma (requires chains o bs es m (-1) /\ b < Seq.length bs /\
                    chain_at o es m (-1) b (I32.v (Seq.index bs b) - 1) l /\
                    q < l /\ x == walk o es (I32.v (Seq.index bs b) - 1) q /\
                    Seq.length es' == Seq.length es /\ Seq.length bs' == Seq.length bs /\
                    (forall (j: int). j <> x ==> lvx o es' m x j == lvx o es m (-1) j) /\
                    (let p = prev o es (I32.v (Seq.index bs b) - 1) q in
                     (forall (j: int). lvx o es m (-1) j /\ j <> x ==>
                        o.hc (Seq.index es' j) == o.hc (Seq.index es j) /\
                        (j <> p \/ q = 0 ==> o.nx (Seq.index es' j) == o.nx (Seq.index es j))) /\
                     (if q = 0
                      then same_but bs bs' b /\ I32.v (Seq.index bs' b) == o.nx (Seq.index es x) + 1
                      else bs' == bs /\ o.nx (Seq.index es' p) == o.nx (Seq.index es x))))
          (ensures chains o bs' es' m x)
  = let h = I32.v (Seq.index bs b) - 1 in
    let h' = if q = 0 then walk o es h 1 else h in
    assert (lvx o es m (-1) x /\ in_bucket o es b x);
    let one (b': nat) : Lemma (b' < Seq.length bs' ==> bucket_ok o bs' es' m x b') =
      if b' < Seq.length bs' then begin
        if b' <> b then begin
          assert (bucket_ok o bs es m (-1) b');
          if q > 0 then assert (lvx o es m (-1) (prev o es h q) /\ in_bucket o es b (prev o es h q));
          bucket_frame o bs bs' es es' m (-1) m x b'
        end else begin
          let w (r: nat) : Lemma (requires r <= l - 1)
                                (ensures walk o es' h' r == walk o es h (skip q r)) =
            unlink_walk o es es' m b h l q x h' r
          in
          w (l - 1);
          assert (I32.v (Seq.index bs' b) - 1 == h');
          let lv (r: nat) : Lemma (requires r < l - 1)
                                  (ensures lvx o es' m x (walk o es' h' r) &&
                                           in_bucket o es' b (walk o es' h' r)) =
            w r;
            let j = walk o es h (skip q r) in
            assert (lvx o es m (-1) j /\ in_bucket o es b j);
            assert (j <> x)
          in
          FStar.Classical.forall_intro (FStar.Classical.move_requires lv);
          let d (r1 r2: nat) : Lemma (requires r1 < r2 /\ r2 < l - 1)
                                     (ensures walk o es' h' r1 <> walk o es' h' r2) =
            w r1; w r2;
            assert (walk o es h (skip q r1) <> walk o es h (skip q r2))
          in
          FStar.Classical.forall_intro_2 (fun r1 r2 -> FStar.Classical.move_requires (d r1) r2);
          assert (chain_at o es' m x b h' (l - 1));
          let c (j: int) : Lemma (requires lvx o es' m x j /\ in_bucket o es' b j)
                                 (ensures exists (r: nat). r < l - 1 /\ walk o es' h' r == j) =
            assert (lvx o es m (-1) j /\ in_bucket o es b j);
            let q' = FStar.IndefiniteDescription.indefinite_description_ghost nat
                       (fun q' -> q' < l /\ walk o es h q' == j) in
            let r = if q' < q then q' else q' - 1 in
            w r;
            assert (skip q r == q')
          in
          FStar.Classical.forall_intro (FStar.Classical.move_requires c);
          assert (complete_at o es' m x b h' (l - 1))
        end
      end
    in
    FStar.Classical.forall_intro one

(* ---------------------------------------------------------------------------------- *)
(* Remove *)

/// Remove's search state: `search`, with `last` the node before `i` (-1 at the head).
let search_last (#e #k: Type0) (o: ops e k) (c: Eq.handle) (bs: seq I32.t) (es: seq e)
                (n fl fc: int) (x: k) (i: int) (q: nat) (last: int)
  : prop
  = search o c bs es n fl fc x i q /\
    last == (if q = 0 then -1 else walk o es (I32.v (Seq.index bs (bkt (hv c x) (Seq.length es))) - 1) (q - 1))

let search_last_start (#e #k: Type0) (o: ops e k) (c: Eq.handle) (bs: seq I32.t) (es: seq e)
                      (n fl fc: int) (x: k)
  : Lemma (requires wf o c bs es n fl fc /\ Seq.length es > 0)
          (ensures search_last o c bs es n fl fc x (I32.v (Seq.index bs (bkt (hv c x) (Seq.length es))) - 1) 0 (-1))
  = search_start o c bs es n fl fc x

let search_last_step (#e #k: Type0) (o: ops e k) (c: Eq.handle) (bs: seq I32.t) (es: seq e)
                     (n fl fc: int) (x: k) (i: int) (q: nat) (last: int)
  : Lemma (requires search_last o c bs es n fl fc x i q last /\ inr es i /\ not (hit o c es (hv c x) x i))
          (ensures search_last o c bs es n fl fc x (o.nx (Seq.index es i)) (q + 1) i /\
                   q + 1 <= Seq.length es)
  = search_step o c bs es n fl fc x i q

/// The writes `Remove` makes on finding `x` at the live entry `i`, with predecessor
/// `last`: the chain is linked past `i` (through the bucket, or through `last`), and `i`
/// is pushed on the free list. Nothing else changes, but `i`'s other fields.
let remove_writes (#e #k: Type0) (o: ops e k) (bs bs': seq I32.t) (es es': seq e)
                  (b: nat) (fl i last: int)
  : prop
  = Seq.length es' == Seq.length es /\ Seq.length bs' == Seq.length bs /\ inr es i /\
    (forall (j: nat). {:pattern Seq.index es' j}
       j < Seq.length es /\ j <> i /\ j <> last ==> Seq.index es' j == Seq.index es j) /\
    (last >= 0 ==> inr es last /\ last <> i /\
                   o.nx (Seq.index es' last) == o.nx (Seq.index es i) /\
                   o.hc (Seq.index es' last) == o.hc (Seq.index es last) /\
                   o.key (Seq.index es' last) == o.key (Seq.index es last)) /\
    o.nx (Seq.index es' i) == -3 - fl /\
    (if last < 0 then same_but bs bs' b /\ I32.v (Seq.index bs' b) == o.nx (Seq.index es i) + 1
     else bs' == bs)

#push-options "--z3rlimit 40"
let remove_ok (#e #k: Type0) (o: ops e k) (c: Eq.handle) (bs bs': seq I32.t) (es es': seq e)
              (n fl fc: int) (x: k) (i: int) (q: nat) (last: int)
  : Lemma (requires search_last o c bs es n fl fc x i q last /\ hit o c es (hv c x) x i /\
                    remove_writes o bs bs' es es' (bkt (hv c x) (Seq.length es)) fl i last)
          (ensures 0 <= i /\ i < n /\ n <= Seq.length es /\
                   pos o es i < Seq.length (items o es n (-1)) /\
                   wf o c bs' es' n i (fc + 1) /\
                   items o es' n (-1) == remove_at (items o es n (-1)) (pos o es i) /\
                   Eq.equals c (Seq.index (items o es n (-1)) (pos o es i)) x)
  = let len = Seq.length es in
    let b = bkt (hv c x) len in
    let h = I32.v (Seq.index bs b) - 1 in
    let l = chain_of o c bs es n fl fc b in
    search_found o c bs es n fl fc x i q;
    if q >= l then walk_end o es h l q;
    assert (q < l);
    if q > 0 then begin
      chain_live o es n (-1) b h l (q - 1);
      chain_distinct o es n (-1) b h l (q - 1) q;
      assert (last == prev o es h q)
    end;
    fl_range o es n (-1) fl fc;
    assert (forall (j: int). j <> i ==> lvx o es' n i j == lvx o es n (-1) j);
    chains_unlink o bs bs' es es' n b l q i;
    chains_same o bs' es' es' n i n (-1);
    items_hole o es n i;
    items_hole o es' n i;
    items_frame o es es' n i;
    free_same o es es' n (-1) i fl fc;
    free_push o es' n i fl fc;
    remove_insert (items o es n i) (pos o es i) (o.key (Seq.index es i));
    items_index o es n i
#pop-options

/// The entry a search stops at in range links on to an entry in range, or to the end:
/// `entry.Next + 1` cannot overflow; nor can `StartOfFreeList - _freeList`, the free list
/// being in range too.
let search_next (#e #k: Type0) (o: ops e k) (c: Eq.handle) (bs: seq I32.t) (es: seq e)
                (n fl fc: int) (x: k) (i: int) (q: nat)
  : Lemma (requires search o c bs es n fl fc x i q /\ inr es i)
          (ensures -1 <= o.nx (Seq.index es i) /\ o.nx (Seq.index es i) < Seq.length es /\
                   -1 <= fl /\ fl < Seq.length es)
  = fl_range o es n (-1) fl fc;
    let b = bkt (hv c x) (Seq.length es) in
    let h = I32.v (Seq.index bs b) - 1 in
    let l = chain_of o c bs es n fl fc b in
    if q >= l then walk_end o es h l q;
    assert (walk o es h (q + 1) == nxt o es i);
    if q + 1 < l then assert (lvx o es n (-1) (walk o es h (q + 1)))
