module OrderedDictionaryChain

/// The glue between `OrderedDictionary<TKey,TValue>`'s representation, as pal-csharp
/// translates it, and the separate-chaining theory in `Pulse.Lib.CSharp.HashChain`
/// (doc/translation.md §33). Every definition here is a definition; nothing is assumed.
///
/// `OrderedDictionary` keeps no free list: removing an entry shifts the ones above it down,
/// so the first `_count` entries are exactly the pairs, in order, and every one of them is
/// in a chain. The table is `HashChain.wf` with an empty free list (`-1`, `0`).

open FStar.Seq
module Seq = FStar.Seq
module I32 = FStar.Int32
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module HC = Pulse.Lib.CSharp.HashChain
module Eq = Pulse.Lib.CSharp.Equality
module E = Struct_OrderedDictionary_Entry

/// `ulong.MaxValue / divisor + 1`, wrapped (it is 0 for `divisor == 1`).
let multiplier (d: int) : int =
  if d <= 0 then 0 else ((pow2 64 - 1) / d + 1) % pow2 64

let entry (tk tv: Type0) = E.struct_OrderedDictionary_Entry tk tv

/// `Entry.HashCode` is a `uint`; the theory's hash codes are `int`s. The stored code is
/// `(uint)hash`, which `sx` takes back to `hash`.
let sx (u: U32.t) : int = if U32.v u >= pow2 31 then U32.v u - pow2 32 else U32.v u

/// `Entry.HashCode`, `Entry.Next` and `Entry.Key`.
let ops (tk tv: Type0) : HC.ops (entry tk tv) tk = {
  HC.hc = (fun (x: entry tk tv) -> sx x.E.fld_HashCode);
  HC.nx = (fun (x: entry tk tv) -> I32.v x.E.fld_Next);
  HC.key = (fun (x: entry tk tv) -> x.E.fld_Key);
}

/// The comparer the dictionary uses: `_comparer`, or `EqualityComparer<TKey>.Default` when
/// it is null, which the constructors allow only for a value type.
let eff (#t: Type0) (c: option (Eq.comparer t)) : Eq.handle =
  match c with
  | None -> Eq.default_comparer t
  | Some h -> h

/// Opaque to the solver: the methods reach it only through the lemmas below, which keeps
/// its quantifiers out of every query that does not need them.
[@@"opaque_to_smt"]
let wf (#tk #tv: Type0) (bs: seq I32.t) (es: seq (entry tk tv)) (n: int) (c: option (Eq.comparer tk)) : prop =
  HC.wf (ops tk tv) (eff c) bs es n (-1) 0

let keys (#tk #tv: Type0) (es: seq (entry tk tv)) (n: int) : seq tk =
  if 0 <= n && n <= Seq.length es then Seq.init n (fun j -> (Seq.index es j).E.fld_Key) else Seq.empty

let values (#tk #tv: Type0) (es: seq (entry tk tv)) (n: int) : seq tv =
  if 0 <= n && n <= Seq.length es then Seq.init n (fun j -> (Seq.index es j).E.fld_Value) else Seq.empty

let mem (#t: Type0) (c: option (Eq.comparer t)) (xs: seq t) (x: t) : prop =
  HC.mem (eff c) xs x

/// The hash code a lookup of `x` computes: `(uint)(comparer?.GetHashCode(x) ?? x.GetHashCode())`.
let hash_of (#t: Type0) (c: option (Eq.comparer t)) (x: t) : int = I32.v (Eq.hash (eff c) x) % pow2 32

/// `c` deems `k` equal to `x`.
let key_eq (#t: Type0) (c: option (Eq.comparer t)) (k x: t) : bool = Eq.equals (eff c) k x

(* ---------------------------------------------------------------------------------- *)
(* Every entry below the count is live *)

let rec live_all (#tk #tv: Type0) (es: seq (entry tk tv)) (n: nat{n <= Seq.length es}) (j: nat{j < n})
  : Lemma (requires HC.ndead (ops tk tv) es n (-1) == 0)
          (ensures I32.v (Seq.index es j).E.fld_Next >= -1)
          (decreases n)
  = if j = n - 1 then () else live_all es (n - 1) j

let rec items_keys (#tk #tv: Type0) (es: seq (entry tk tv)) (n: nat{n <= Seq.length es})
  : Lemma (requires HC.ndead (ops tk tv) es n (-1) == 0)
          (ensures HC.items (ops tk tv) es n (-1) == keys es n)
          (decreases n)
  = if n = 0 then assert (Seq.equal (keys es 0) Seq.empty)
    else begin
      items_keys es (n - 1);
      assert (Seq.equal (keys es n) (Seq.snoc (keys es (n - 1)) (Seq.index es (n - 1)).E.fld_Key))
    end

let wf_keys (#tk #tv: Type0) (bs: seq I32.t) (es: seq (entry tk tv)) (n: int) (c: option (Eq.comparer tk))
  : Lemma (requires wf bs es n c)
          (ensures 0 <= n /\ n <= Seq.length es /\ HC.items (ops tk tv) es n (-1) == keys es n /\
                   (forall (j: nat). j < n ==> j < Seq.length es /\ I32.v (Seq.index es j).E.fld_Next >= -1))
  = reveal_opaque (`%wf) (wf #tk #tv);
    items_keys es n;
    let aux (j: nat) : Lemma (j < n ==> j < Seq.length es /\ I32.v (Seq.index es j).E.fld_Next >= -1) =
      if j < n then live_all es n j
    in
    FStar.Classical.forall_intro aux

(* ---------------------------------------------------------------------------------- *)
(* IndexOf *)

/// The bucket `x` hashes to, as stored (1-based).
let bucket (#tk #tv: Type0) (bs: seq I32.t) (es: seq (entry tk tv)) (c: option (Eq.comparer tk)) (x: tk) : int =
  if Seq.length es > 0 && Seq.length bs = Seq.length es
  then I32.v (Seq.index bs (hash_of c x % Seq.length es))
  else 0

/// The search for `x` has followed `q` links of its chain to `i`, passing no hit.
[@@"opaque_to_smt"]
let search (#tk #tv: Type0) (bs: seq I32.t) (es: seq (entry tk tv)) (n: int) (c: option (Eq.comparer tk))
           (x: tk) (i q: int) : prop =
  q >= 0 /\ HC.search (ops tk tv) (eff c) bs es n (-1) 0 x i q

/// Entry `i` stores `x`'s hash code and a key `c` deems equal to `x`: what `IndexOf` stops at.
let hit (#tk #tv: Type0) (es: seq (entry tk tv)) (c: option (Eq.comparer tk)) (x: tk) (i: int) : bool =
  0 <= i && i < Seq.length es &&
  U32.v (Seq.index es i).E.fld_HashCode = hash_of c x &&
  Eq.equals (eff c) (Seq.index es i).E.fld_Key x

let sx_hash (u: U32.t) (h: I32.t)
  : Lemma ((U32.v u = I32.v h % pow2 32) <==> (sx u = I32.v h))
  = ()

let hit_hc (#tk #tv: Type0) (es: seq (entry tk tv)) (c: option (Eq.comparer tk)) (x: tk) (i: int)
  : Lemma (hit es c x i == HC.hit (ops tk tv) (eff c) es (HC.hv (eff c) x) x i)
  = if 0 <= i && i < Seq.length es then sx_hash (Seq.index es i).E.fld_HashCode (Eq.hash (eff c) x)

let search_start (#tk #tv: Type0) (bs: seq I32.t) (es: seq (entry tk tv)) (n: int) (c: option (Eq.comparer tk)) (x: tk)
  : Lemma (requires wf bs es n c /\ Seq.length es > 0)
          (ensures search bs es n c x (bucket bs es c x - 1) 0 /\
                   0 <= bucket bs es c x /\ bucket bs es c x <= Seq.length es)
  = reveal_opaque (`%wf) (wf #tk #tv); reveal_opaque (`%search) (search #tk #tv);
    HC.search_start (ops tk tv) (eff c) bs es n (-1) 0 x

let search_step (#tk #tv: Type0) (bs: seq I32.t) (es: seq (entry tk tv)) (n: int) (c: option (Eq.comparer tk))
                (x: tk) (i q: int)
  : Lemma (requires search bs es n c x i q /\ 0 <= i /\ i < Seq.length es /\ ~ (hit es c x i))
          (ensures search bs es n c x (I32.v (Seq.index es i).E.fld_Next) (q + 1) /\
                   q + 1 <= Seq.length es)
  = reveal_opaque (`%search) (search #tk #tv);
    hit_hc es c x i;
    HC.search_step (ops tk tv) (eff c) bs es n (-1) 0 x i q

let search_hit (#tk #tv: Type0) (bs: seq I32.t) (es: seq (entry tk tv)) (n: int) (c: option (Eq.comparer tk))
               (x: tk) (i q: int)
  : Lemma (requires search bs es n c x i q /\ hit es c x i)
          (ensures 0 <= i /\ i < n /\ i < Seq.length (keys es n) /\
                   (i < Seq.length (keys es n) ==> key_eq c (Seq.index (keys es n) i) x) /\ mem c (keys es n) x)
  = reveal_opaque (`%search) (search #tk #tv);
    hit_hc es c x i;
    HC.search_found (ops tk tv) (eff c) bs es n (-1) 0 x i q;
    reveal_opaque (`%wf) (wf #tk #tv);
    wf_keys bs es n c

let search_absent (#tk #tv: Type0) (bs: seq I32.t) (es: seq (entry tk tv)) (n: int) (c: option (Eq.comparer tk))
                  (x: tk) (i q: int)
  : Lemma (requires search bs es n c x i q /\ ~ (0 <= i /\ i < Seq.length es))
          (ensures ~ (mem c (keys es n) x))
  = reveal_opaque (`%search) (search #tk #tv);
    reveal_opaque (`%wf) (wf #tk #tv);
    wf_keys bs es n c;
    let aux (p: nat) : Lemma (p < Seq.length (keys es n) ==> not (Eq.equals (eff c) (Seq.index (keys es n) p) x)) =
      if p < Seq.length (keys es n) then HC.search_none (ops tk tv) (eff c) bs es n (-1) 0 x i q p
    in
    FStar.Classical.forall_intro aux

(* ---------------------------------------------------------------------------------- *)
(* Changes that keep the table *)

/// A change to the entries that keeps every pair's link, hash code and key below the count
/// (`SetAt(index, value)`) keeps the table and its keys.
let wf_frame (#tk #tv: Type0) (bs: seq I32.t) (es es': seq (entry tk tv)) (n: int) (c: option (Eq.comparer tk))
  : Lemma (requires wf bs es n c /\ Seq.length es' == Seq.length es /\
                    (forall (j: nat). j < n /\ j < Seq.length es ==>
                       (Seq.index es' j).E.fld_Next == (Seq.index es j).E.fld_Next /\
                       (Seq.index es' j).E.fld_HashCode == (Seq.index es j).E.fld_HashCode /\
                       (Seq.index es' j).E.fld_Key == (Seq.index es j).E.fld_Key))
          (ensures wf bs es' n c /\ keys es' n == keys es n)
  = reveal_opaque (`%wf) (wf #tk #tv);
    let o = ops tk tv in
    let same (j: int) : Lemma (HC.lvx o es n (-1) j == HC.lvx o es' n (-1) j /\
                               (HC.lvx o es n (-1) j ==>
                                  o.HC.nx (Seq.index es' j) == o.HC.nx (Seq.index es j) /\
                                  o.HC.hc (Seq.index es' j) == o.HC.hc (Seq.index es j) /\
                                  o.HC.key (Seq.index es' j) == o.HC.key (Seq.index es j))) = ()
    in
    FStar.Classical.forall_intro same;
    HC.chains_same o bs es es' n (-1) n (-1);
    HC.items_frame o es es' n (-1);
    assert (Seq.equal (keys es' n) (keys es n))

/// `Array.Clear(_buckets)` and `_count = 0`.
let wf_clear (#tk #tv: Type0) (bs: seq I32.t) (es: seq (entry tk tv)) (c: option (Eq.comparer tk))
  : Lemma (requires Seq.length bs == Seq.length es /\
                    (forall (b: nat). b < Seq.length bs ==> I32.v (Seq.index bs b) == 0))
          (ensures wf bs es 0 c /\ keys es 0 == Seq.empty /\ values es 0 == Seq.empty)
  = reveal_opaque (`%wf) (wf #tk #tv);
    HC.wf_empty (ops tk tv) (eff c) bs es;
    assert (Seq.equal (keys es 0) Seq.empty);
    assert (Seq.equal (values es 0) Seq.empty)

/// An empty table is well formed whatever the comparer: the constructor sets `_comparer`
/// after `EnsureBucketsAndEntriesInitialized` built the table.
let wf_rebind (#tk #tv: Type0) (bs: seq I32.t) (es: seq (entry tk tv)) (c c': option (Eq.comparer tk))
  : Lemma (wf bs es 0 c ==> wf bs es 0 c')
  = reveal_opaque (`%wf) (wf #tk #tv)

/// `_entries[i].Value = v`.
let set_value (#tk #tv: Type0) (es: seq (entry tk tv)) (i: int) (v: tv) : seq (entry tk tv) =
  if 0 <= i && i < Seq.length es then Seq.upd es i { Seq.index es i with E.fld_Value = v } else es

let wf_set_value (#tk #tv: Type0) (bs: seq I32.t) (es: seq (entry tk tv)) (n: int) (c: option (Eq.comparer tk))
                 (i: int) (v: tv)
  : Lemma (requires wf bs es n c /\ 0 <= i /\ i < n)
          (ensures wf bs (set_value es i v) n c /\ keys (set_value es i v) n == keys es n /\
                   n <= Seq.length es /\ i < Seq.length (values es n) /\
                   values (set_value es i v) n == Seq.upd (values es n) i v)
  = reveal_opaque (`%wf) (wf #tk #tv);
    wf_frame bs es (set_value es i v) n c;
    reveal_opaque (`%wf) (wf #tk #tv);
    assert (Seq.equal (values (set_value es i v) n) (Seq.upd (values es n) i v))

/// `EqualityComparer<TValue>.Default.Equals(x, vs[p])` for some `p < i`.
let has_value (#t: Type0) (vs: seq t) (x: t) (i: int) : prop =
  exists (p: nat). p < i /\ p < Seq.length vs /\ Eq.equals (Eq.default_comparer t) x (Seq.index vs p)

(* ---------------------------------------------------------------------------------- *)
(* Shifting: the table with a hole *)

/// `Insert` and `RemoveAt` move the entries above an index one place, fixing the chains as
/// they go. In between, one entry `h` below the limit `m` is in no chain: the hole the next
/// entry moves into. `wfm` is that state, and `keysh`/`valuesh` the pairs it holds, in order.

let rec ndead_zero (#tk #tv: Type0) (es: seq (entry tk tv)) (n: nat{n <= Seq.length es}) (hole: int)
  : Lemma (requires forall (j: nat). j < n /\ j <> hole ==> I32.v (Seq.index es j).E.fld_Next >= -1)
          (ensures HC.ndead (ops tk tv) es n hole == 0)
          (decreases n)
  = if n = 0 then () else ndead_zero es (n - 1) hole

[@@"opaque_to_smt"]
let wfm_core (#tk #tv: Type0) (bs: seq I32.t) (es: seq (entry tk tv)) (m h: int) (c: option (Eq.comparer tk)) : prop =
  HC.chains (ops tk tv) bs es m h /\
  (forall (j: nat). j < m /\ j < Seq.length es /\ j <> h ==> I32.v (Seq.index es j).E.fld_Next >= -1) /\
  HC.hashes_ok (ops tk tv) (eff c) es m h

let wfm (#tk #tv: Type0) (bs: seq I32.t) (es: seq (entry tk tv)) (m h: int) (c: option (Eq.comparer tk)) : prop =
  0 <= h /\ h < m /\ m <= Seq.length es /\ Seq.length bs == Seq.length es /\ wfm_core bs es m h c

let skip1 (h j: int) : int = if j < h then j else j + 1

let keysh (#tk #tv: Type0) (es: seq (entry tk tv)) (m h: int) : seq tk =
  if 0 <= h && h < m && m <= Seq.length es
  then Seq.init (m - 1) (fun (j: nat{j < m - 1}) -> (Seq.index es (skip1 h j)).E.fld_Key)
  else Seq.empty

let valuesh (#tk #tv: Type0) (es: seq (entry tk tv)) (m h: int) : seq tv =
  if 0 <= h && h < m && m <= Seq.length es
  then Seq.init (m - 1) (fun (j: nat{j < m - 1}) -> (Seq.index es (skip1 h j)).E.fld_Value)
  else Seq.empty

/// Entries `h` and `i` are the same: `entries[h] = entries[i]` has just run.
let copied (#tk #tv: Type0) (es: seq (entry tk tv)) (h i: int) : prop =
  0 <= h /\ h < Seq.length es /\ 0 <= i /\ i < Seq.length es /\ Seq.index es h == Seq.index es i

/// `es'` is `es` but for links: what fixing a chain changes.
let same_data (#tk #tv: Type0) (es es': seq (entry tk tv)) : prop =
  Seq.length es' == Seq.length es /\
  (forall (j: nat). {:pattern Seq.index es' j} j < Seq.length es ==>
     (Seq.index es' j).E.fld_Key == (Seq.index es j).E.fld_Key /\
     (Seq.index es' j).E.fld_Value == (Seq.index es j).E.fld_Value /\
     (Seq.index es' j).E.fld_HashCode == (Seq.index es j).E.fld_HashCode)

/// `Insert` opens a hole at the end.
let open_ok (#tk #tv: Type0) (bs: seq I32.t) (es: seq (entry tk tv)) (n: int) (c: option (Eq.comparer tk))
  : Lemma (requires wf bs es n c /\ n < Seq.length es)
          (ensures wfm bs es (n + 1) n c /\ keysh es (n + 1) n == keys es n /\ valuesh es (n + 1) n == values es n)
  = reveal_opaque (`%wf) (wf #tk #tv);
    reveal_opaque (`%wfm_core) (wfm_core #tk #tv);
    let o = ops tk tv in
    wf_keys bs es n c;
    HC.chains_same o bs es es n (-1) (n + 1) n;
    let hs (j: int) : Lemma (HC.lvx o es (n + 1) n j ==>
                              o.HC.hc (Seq.index es j) == HC.hv (eff c) (o.HC.key (Seq.index es j))) =
      assert (HC.lvx o es (n + 1) n j == HC.lvx o es n (-1) j)
    in
    FStar.Classical.forall_intro hs;
    assert (Seq.equal (keysh es (n + 1) n) (keys es n));
    assert (Seq.equal (valuesh es (n + 1) n) (values es n))

/// Whatever the hole holds is no pair.
let hole_set (#tk #tv: Type0) (bs: seq I32.t) (es: seq (entry tk tv)) (m h: int) (c: option (Eq.comparer tk))
             (x: entry tk tv)
  : Lemma (requires wfm bs es m h c)
          (ensures wfm bs (Seq.upd es h x) m h c /\ keysh (Seq.upd es h x) m h == keysh es m h /\
                   valuesh (Seq.upd es h x) m h == valuesh es m h)
  = reveal_opaque (`%wfm_core) (wfm_core #tk #tv);
    let o = ops tk tv in
    let es' = Seq.upd es h x in
    HC.chains_same o bs es es' m h m h;
    let hs (j: int) : Lemma (HC.lvx o es' m h j ==>
                              o.HC.hc (Seq.index es' j) == HC.hv (eff c) (o.HC.key (Seq.index es' j))) =
      assert (HC.lvx o es' m h j == HC.lvx o es m h j)
    in
    FStar.Classical.forall_intro hs;
    assert (Seq.equal (keysh es' m h) (keysh es m h));
    assert (Seq.equal (valuesh es' m h) (valuesh es m h))

/// `RemoveAt` closes the hole at the end.
let close_ok (#tk #tv: Type0) (bs: seq I32.t) (es: seq (entry tk tv)) (n: int) (c: option (Eq.comparer tk))
             (x: entry tk tv)
  : Lemma (requires wfm bs es n (n - 1) c)
          (ensures wf bs (Seq.upd es (n - 1) x) (n - 1) c /\
                   keys (Seq.upd es (n - 1) x) (n - 1) == keysh es n (n - 1) /\
                   values (Seq.upd es (n - 1) x) (n - 1) == valuesh es n (n - 1))
  = reveal_opaque (`%wf) (wf #tk #tv);
    reveal_opaque (`%wfm_core) (wfm_core #tk #tv);
    let o = ops tk tv in
    let es' = Seq.upd es (n - 1) x in
    HC.chains_same o bs es es' n (n - 1) (n - 1) (-1);
    ndead_zero es' (n - 1) (-1);
    let hs (j: int) : Lemma (HC.lvx o es' (n - 1) (-1) j ==>
                              o.HC.hc (Seq.index es' j) == HC.hv (eff c) (o.HC.key (Seq.index es' j))) =
      assert (HC.lvx o es' (n - 1) (-1) j == HC.lvx o es n (n - 1) j)
    in
    FStar.Classical.forall_intro hs;
    assert (Seq.equal (keys es' (n - 1)) (keysh es n (n - 1)));
    assert (Seq.equal (values es' (n - 1)) (valuesh es n (n - 1)))

(* ---------------------------------------------------------------------------------- *)
(* Finding an entry's predecessor in its chain *)

/// The bucket of entry `i`.
let bof (#tk #tv: Type0) (es: seq (entry tk tv)) (i: int) : int =
  if 0 <= i && i < Seq.length es then U32.v (Seq.index es i).E.fld_HashCode % Seq.length es else 0

let bkt_sx (u: U32.t) (len: pos) : Lemma (HC.bkt (sx u) len == U32.v u % len) = ()

/// The head of the chain of entry `t`'s bucket.
let head (#tk #tv: Type0) (bs: seq I32.t) (es: seq (entry tk tv)) (t: int) : int =
  if Seq.length bs = Seq.length es && 0 <= t && t < Seq.length es then I32.v (Seq.index bs (bof es t)) - 1 else -1

/// The walk from the head of `t`'s chain, with `m` and hole `h`, has reached `i` after `q`
/// links, and `t` is further on.
[@@"opaque_to_smt"]
let pred (#tk #tv: Type0) (bs: seq I32.t) (es: seq (entry tk tv)) (m h t i q: int) : prop =
  Seq.length es > 0 /\ Seq.length bs == Seq.length es /\ 0 <= t /\ t < Seq.length es /\ q >= 0 /\
  (exists (l qt: nat). HC.chain_at (ops tk tv) es m h (bof es t) (head bs es t) l /\
                     qt < l /\ HC.walk (ops tk tv) es (head bs es t) qt == t /\ q < qt /\
                     i == HC.walk (ops tk tv) es (head bs es t) q)

let in_bucket_bof (#tk #tv: Type0) (es: seq (entry tk tv)) (t: int)
  : Lemma (requires 0 <= t /\ t < Seq.length es)
          (ensures HC.in_bucket (ops tk tv) es (bof es t) t)
  = bkt_sx (Seq.index es t).E.fld_HashCode (Seq.length es)

/// A chain node is found by the walk from its bucket's head.
let find_in_chain (#tk #tv: Type0) (bs: seq I32.t) (es: seq (entry tk tv)) (m h t: int)
  : Ghost (nat & nat)
          (requires HC.chains (ops tk tv) bs es m h /\ HC.lvx (ops tk tv) es m h t)
          (ensures fun (l, qt) -> HC.chain_at (ops tk tv) es m h (bof es t) (head bs es t) l /\
                                 HC.complete_at (ops tk tv) es m h (bof es t) (head bs es t) l /\
                                 qt < l /\ HC.walk (ops tk tv) es (head bs es t) qt == t)
  = let o = ops tk tv in
    let b = bof es t in
    in_bucket_bof es t;
    assert (HC.bucket_ok o bs es m h b);
    let hd = head bs es t in
    let l = FStar.IndefiniteDescription.indefinite_description_ghost nat
              (fun l -> HC.chain_at o es m h b hd l /\ HC.complete_at o es m h b hd l) in
    let qt = FStar.IndefiniteDescription.indefinite_description_ghost nat
              (fun qt -> qt < l /\ HC.walk o es hd qt == t) in
    (l, qt)

/// The walk starts at the head; if that is not `t`, it has a predecessor to find.
let pred_start (#tk #tv: Type0) (bs: seq I32.t) (es: seq (entry tk tv)) (m h t: int)
  : Lemma (requires HC.chains (ops tk tv) bs es m h /\ HC.lvx (ops tk tv) es m h t /\
                    I32.v (Seq.index bs (bof es t)) <> t + 1)
          (ensures pred bs es m h t (head bs es t) 0)
  = reveal_opaque (`%pred) (pred #tk #tv);
    let (l, qt) = find_in_chain bs es m h t in
    ()

let pred_range (#tk #tv: Type0) (bs: seq I32.t) (es: seq (entry tk tv)) (m h t i q: int)
  : Lemma (requires pred bs es m h t i q)
          (ensures 0 <= i /\ i < Seq.length es /\ q < Seq.length es)
  = reveal_opaque (`%pred) (pred #tk #tv)

let pred_step (#tk #tv: Type0) (bs: seq I32.t) (es: seq (entry tk tv)) (m h t i q: int)
  : Lemma (requires pred bs es m h t i q /\ 0 <= i /\ i < Seq.length es /\
                    I32.v (Seq.index es i).E.fld_Next <> t)
          (ensures pred bs es m h t (I32.v (Seq.index es i).E.fld_Next) (q + 1) /\ q + 1 < Seq.length es)
  = reveal_opaque (`%pred) (pred #tk #tv);
    let o = ops tk tv in
    let hd = head bs es t in
    let l = FStar.IndefiniteDescription.indefinite_description_ghost nat (fun l ->
              exists (qt: nat). HC.chain_at o es m h (bof es t) hd l /\ qt < l /\ HC.walk o es hd qt == t /\
                               q < qt /\ i == HC.walk o es hd q) in
    let qt = FStar.IndefiniteDescription.indefinite_description_ghost nat (fun qt ->
              HC.chain_at o es m h (bof es t) hd l /\ qt < l /\ HC.walk o es hd qt == t /\
              q < qt /\ i == HC.walk o es hd q) in
    assert (HC.walk o es hd (q + 1) == HC.nxt o es i);
    assert (q + 1 <> qt)

(* ---------------------------------------------------------------------------------- *)
(* Moving an entry one place (UpdateBucketIndex) *)

/// `σ`: the entry `i` has moved to `h`.
let sigma (i h j: int) : int = if j = i then h else j

/// What `UpdateBucketIndex` does to the chain of the bucket `b` of the entry `i` that moved
/// to `h`: the head, or the link of the predecessor `p` (the `qp`th node), now leads to `h`,
/// whose link is `i`'s.
[@@"opaque_to_smt"]
let moved (#tk #tv: Type0) (es es': seq (entry tk tv)) (m h i b hd hd': int) (l: nat) (p: int) (qp: nat) : prop =
  HC.chain_at (ops tk tv) es m h b hd l /\ Seq.length es' == Seq.length es /\
  0 <= h /\ h < Seq.length es /\ HC.lvx (ops tk tv) es m h i /\
  I32.v (Seq.index es' h).E.fld_Next == I32.v (Seq.index es i).E.fld_Next /\
  hd' == sigma i h hd /\
  (if p < 0 then hd == i
   else qp + 1 < l /\ p == HC.walk (ops tk tv) es hd qp /\
        HC.walk (ops tk tv) es hd (qp + 1) == i /\
        I32.v (Seq.index es' p).E.fld_Next == h) /\
  (forall (j: nat). j < Seq.length es /\ j <> h /\ j <> p ==>
     (Seq.index es' j).E.fld_Next == (Seq.index es j).E.fld_Next)

#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
let move_step (#tk #tv: Type0) (es es': seq (entry tk tv)) (m h i b hd hd': int) (l: nat) (p: int) (qp: nat)
              (qi: nat) (q: pos)
  : Lemma (requires moved es es' m h i b hd hd' l p qp /\ q <= l /\ qi < l /\ HC.walk (ops tk tv) es hd qi == i /\
                    HC.walk (ops tk tv) es' hd' (q - 1) == sigma i h (HC.walk (ops tk tv) es hd (q - 1)))
          (ensures HC.walk (ops tk tv) es' hd' q == sigma i h (HC.walk (ops tk tv) es hd q))
  = reveal_opaque (`%moved) (moved #tk #tv);
    let o = ops tk tv in
    let w = HC.walk o es hd (q - 1) in
    assert (HC.lvx o es m h w);
    assert (HC.walk o es hd q == HC.nxt o es w);
    assert (HC.walk o es' hd' q == HC.nxt o es' (sigma i h w));
    if w = i then begin
      assert (q - 1 == qi);
      if q < l then assert (HC.walk o es hd q <> i)
      else assert (HC.walk o es hd q == -1)
    end else if p >= 0 && w = p then begin
      assert (q - 1 == qp)
    end else begin
      assert (w <> h);
      if HC.walk o es hd q = i && q < l then begin
        assert (q == qi);
        if p < 0 then assert (HC.walk o es hd 0 == i)
        else assert (qp + 1 == q)
      end
    end

let rec move_walk (#tk #tv: Type0) (es es': seq (entry tk tv)) (m h i b hd hd': int) (l: nat) (p: int) (qp: nat)
                  (qi: nat) (q: nat)
  : Lemma (requires moved es es' m h i b hd hd' l p qp /\ q <= l /\ qi < l /\ HC.walk (ops tk tv) es hd qi == i)
          (ensures HC.walk (ops tk tv) es' hd' q == sigma i h (HC.walk (ops tk tv) es hd q))
          (decreases q)
  = if q = 0 then reveal_opaque (`%moved) (moved #tk #tv)
    else begin
      move_walk es es' m h i b hd hd' l p qp qi (q - 1);
      move_step es es' m h i b hd hd' l p qp qi q
    end
#pop-options

let same_but (bs bs': seq I32.t) (b: int) : prop =
  0 <= b /\ HC.same_but bs bs' b

/// The changes `UpdateBucketIndex(i, h - i)` makes, `h` being the hole and `entries[h]`
/// already a copy of `entries[i]`: through the head of `i`'s bucket if `i` is it (`p < 0`),
/// otherwise through the predecessor `p`, which the search found after `q` links.
let move_writes (#tk #tv: Type0) (bs bs': seq I32.t) (es es': seq (entry tk tv)) (m h i p q: int) : prop =
  Seq.length es > 0 /\ Seq.length bs == Seq.length es /\
  Seq.length es' == Seq.length es /\ Seq.length bs' == Seq.length bs /\
  0 <= i /\ i < Seq.length es /\ 0 <= h /\ h < Seq.length es /\
  (if p < 0
   then I32.v (Seq.index bs (bof es i)) == i + 1 /\ es' == es /\
        same_but bs bs' (bof es i) /\ I32.v (Seq.index bs' (bof es i)) == h + 1
   else pred bs es m h i p q /\ p < Seq.length es /\ I32.v (Seq.index es p).E.fld_Next == i /\ bs' == bs /\
        (forall (j: nat). {:pattern Seq.index es' j} j < Seq.length es /\ j <> p ==> Seq.index es' j == Seq.index es j) /\
        I32.v (Seq.index es' p).E.fld_Next == h /\
        (Seq.index es' p).E.fld_HashCode == (Seq.index es p).E.fld_HashCode /\
        (Seq.index es' p).E.fld_Key == (Seq.index es p).E.fld_Key /\
        (Seq.index es' p).E.fld_Value == (Seq.index es p).E.fld_Value)

/// The live nodes before and after the move: `σ` maps one onto the other, buckets kept.
let move_live (#tk #tv: Type0) (es es': seq (entry tk tv)) (m h i b hd hd': int) (l: nat) (p: int) (qp: nat) (x: int)
  : Lemma (requires moved es es' m h i b hd hd' l p qp /\ same_data es es' /\ copied es h i /\ HC.lvx (ops tk tv) es m h x /\ h < m)
          (ensures HC.lvx (ops tk tv) es' m i (sigma i h x) /\
                   (HC.in_bucket (ops tk tv) es' b (sigma i h x) <==> HC.in_bucket (ops tk tv) es b x))
  = reveal_opaque (`%moved) (moved #tk #tv);
    let o = ops tk tv in
    let y = sigma i h x in
    assert ((Seq.index es' y).E.fld_HashCode == (Seq.index es x).E.fld_HashCode);
    if x = i then assert (o.HC.nx (Seq.index es' y) == o.HC.nx (Seq.index es x))
    else if x = p then assert (o.HC.nx (Seq.index es' y) == h)
    else assert (o.HC.nx (Seq.index es' y) == o.HC.nx (Seq.index es x))

let move_live_inv (#tk #tv: Type0) (es es': seq (entry tk tv)) (m h i b hd hd': int) (l: nat) (p: int) (qp: nat) (j: int)
  : Lemma (requires moved es es' m h i b hd hd' l p qp /\ same_data es es' /\ copied es h i /\ HC.lvx (ops tk tv) es' m i j)
          (ensures (let x = if j = h then i else j in
                    HC.lvx (ops tk tv) es m h x /\ sigma i h x == j /\
                    (HC.in_bucket (ops tk tv) es' b j <==> HC.in_bucket (ops tk tv) es b x)))
  = reveal_opaque (`%moved) (moved #tk #tv)

let moved_len (#tk #tv: Type0) (es es': seq (entry tk tv)) (m h i b hd hd': int) (l: nat) (p: int) (qp: nat)
  : Lemma (requires moved es es' m h i b hd hd' l p qp)
          (ensures HC.chain_at (ops tk tv) es m h b hd l /\ 0 <= i /\ i <> h /\ Seq.length es' == Seq.length es)
  = reveal_opaque (`%moved) (moved #tk #tv)

#push-options "--z3rlimit 40 --fuel 0 --ifuel 0"
let move_chain (#tk #tv: Type0) (es es': seq (entry tk tv)) (m h i b hd hd': int) (l: nat) (p: int) (qp: nat) (qi: nat)
  : Lemma (requires moved es es' m h i b hd hd' l p qp /\ same_data es es' /\ copied es h i /\
                    qi < l /\ HC.walk (ops tk tv) es hd qi == i /\ HC.complete_at (ops tk tv) es m h b hd l /\ h < m)
          (ensures HC.chain_at (ops tk tv) es' m i b hd' l /\ HC.complete_at (ops tk tv) es' m i b hd' l)
  = let o = ops tk tv in
    moved_len es es' m h i b hd hd' l p qp;
    let w (r: nat) : Lemma (requires r <= l) (ensures HC.walk o es' hd' r == sigma i h (HC.walk o es hd r)) =
      move_walk es es' m h i b hd hd' l p qp qi r
    in
    let lv (r: nat) : Lemma (r < l ==> HC.lvx o es' m i (HC.walk o es' hd' r) && HC.in_bucket o es' b (HC.walk o es' hd' r)) =
      if r < l then begin
        w r;
        let x = HC.walk o es hd r in
        assert (HC.lvx o es m h x /\ HC.in_bucket o es b x);
        move_live es es' m h i b hd hd' l p qp x
      end
    in
    FStar.Classical.forall_intro lv;
    let d (r1 r2: nat) : Lemma (r1 < r2 /\ r2 < l ==> HC.walk o es' hd' r1 <> HC.walk o es' hd' r2) =
      if r1 < r2 && r2 < l then begin
        w r1; w r2;
        HC.chain_distinct o es m h b hd l r1 r2;
        HC.chain_live o es m h b hd l r1;
        HC.chain_live o es m h b hd l r2
      end
    in
    FStar.Classical.forall_intro_2 d;
    w l;
    assert (HC.walk o es hd l == -1);
    assert (HC.chain_at o es' m i b hd' l);
    let cpl (j: int) : Lemma (HC.lvx o es' m i j /\ HC.in_bucket o es' b j ==>
                              (exists (r: nat). r < l /\ HC.walk o es' hd' r == j)) =
      if HC.lvx o es' m i j && HC.in_bucket o es' b j then begin
        move_live_inv es es' m h i b hd hd' l p qp j;
        let x = if j = h then i else j in
        assert (HC.lvx o es m h x /\ HC.in_bucket o es b x);
        let r = FStar.IndefiniteDescription.indefinite_description_ghost nat
                  (fun r -> r < l /\ HC.walk o es hd r == x) in
        w r
      end
    in
    FStar.Classical.forall_intro cpl;
    assert (HC.complete_at o es' m i b hd' l)
#pop-options


/// The node the search found is in the chain of `t`.
let pred_live (#tk #tv: Type0) (bs: seq I32.t) (es: seq (entry tk tv)) (m h t i q: int)
  : Lemma (requires pred bs es m h t i q)
          (ensures HC.lvx (ops tk tv) es m h i /\ HC.in_bucket (ops tk tv) es (bof es t) i)
  = reveal_opaque (`%pred) (pred #tk #tv);
    let o = ops tk tv in
    let hd = head bs es t in
    let l = FStar.IndefiniteDescription.indefinite_description_ghost nat (fun l ->
              exists (qt: nat). HC.chain_at o es m h (bof es t) hd l /\ qt < l /\ HC.walk o es hd qt == t /\
                               q < qt /\ i == HC.walk o es hd q) in
    HC.chain_live o es m h (bof es t) hd l q

/// The predecessor's position in the chain.
let pred_pos (#tk #tv: Type0) (bs: seq I32.t) (es: seq (entry tk tv)) (m h t i q: int) (l: nat)
  : Lemma (requires pred bs es m h t i q /\ HC.chain_at (ops tk tv) es m h (bof es t) (head bs es t) l /\
                    0 <= i /\ i < Seq.length es /\ I32.v (Seq.index es i).E.fld_Next == t)
          (ensures q >= 0 /\ q + 1 < l /\ HC.walk (ops tk tv) es (head bs es t) q == i /\
                   HC.walk (ops tk tv) es (head bs es t) (q + 1) == t)
  = reveal_opaque (`%pred) (pred #tk #tv);
    let o = ops tk tv in
    let hd = head bs es t in
    let l' = FStar.IndefiniteDescription.indefinite_description_ghost nat (fun l' ->
               exists (qt: nat). HC.chain_at o es m h (bof es t) hd l' /\ qt < l' /\ HC.walk o es hd qt == t /\
                                q < qt /\ i == HC.walk o es hd q) in
    HC.chain_len_unique o es m h (bof es t) hd l l';
    assert (HC.walk o es hd (q + 1) == HC.nxt o es i)

#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
let moved_pred (#tk #tv: Type0) (bs bs': seq I32.t) (es es': seq (entry tk tv)) (m h i p q: int) (l: nat)
  : Lemma (requires HC.chain_at (ops tk tv) es m h (bof es i) (head bs es i) l /\ HC.lvx (ops tk tv) es m h i /\
                    0 <= h /\ copied es h i /\ move_writes bs bs' es es' m h i p q /\ p >= 0)
          (ensures q >= 0 /\ moved es es' m h i (bof es i) (head bs es i) (head bs es i) l p q /\ bs' == bs)
  = let o = ops tk tv in
    let hd = head bs es i in
    pred_live bs es m h i p q;
    pred_pos bs es m h i p q l;
    HC.chain_distinct o es m h (bof es i) hd l 0 (q + 1);
    assert (hd <> i /\ p <> h);
    assert (Seq.index es' h == Seq.index es h);
    reveal_opaque (`%moved) (moved #tk #tv)

let moved_head (#tk #tv: Type0) (bs bs': seq I32.t) (es es': seq (entry tk tv)) (m h i p q: int) (l: nat)
  : Lemma (requires HC.chain_at (ops tk tv) es m h (bof es i) (head bs es i) l /\ HC.lvx (ops tk tv) es m h i /\
                    0 <= h /\ copied es h i /\ move_writes bs bs' es es' m h i p q /\ p < 0)
          (ensures moved es es' m h i (bof es i) (head bs es i) h l p 0 /\ I32.v (Seq.index bs' (bof es i)) - 1 == h)
  = reveal_opaque (`%moved) (moved #tk #tv)

let move_bucket (#tk #tv: Type0) (bs bs': seq I32.t) (es es': seq (entry tk tv)) (m h i p q: int) (c: option (Eq.comparer tk))
  : Lemma (requires wfm bs es m h c /\ 0 <= i /\ i < m /\ i <> h /\ copied es h i /\ same_data es es' /\
                    move_writes bs bs' es es' m h i p q)
          (ensures HC.bucket_ok (ops tk tv) bs' es' m i (bof es i))
  = reveal_opaque (`%wfm_core) (wfm_core #tk #tv);
    let o = ops tk tv in
    let b = bof es i in
    let hd = head bs es i in
    in_bucket_bof es i;
    assert (HC.lvx o es m h i);
    let (l, qi) = find_in_chain bs es m h i in
    if p < 0 then begin
      moved_head bs bs' es es' m h i p q l;
      move_chain es es' m h i b hd h l p 0 qi
    end else begin
      moved_pred bs bs' es es' m h i p q l;
      move_chain es es' m h i b hd hd l p q qi
    end
#pop-options

/// What `move_writes` amounts to, entry by entry.
let move_facts (#tk #tv: Type0) (bs bs': seq I32.t) (es es': seq (entry tk tv)) (m h i p q: int) (c: option (Eq.comparer tk))
  : Lemma (requires wfm bs es m h c /\ 0 <= i /\ i < m /\ i <> h /\ copied es h i /\ move_writes bs bs' es es' m h i p q)
          (ensures same_data es es' /\ same_but bs bs' (bof es i) /\ Seq.length es' == Seq.length es /\
                   Seq.index es' h == Seq.index es h /\
                   (forall (j: nat). {:pattern Seq.index es' j} j < Seq.length es /\ j <> p ==> Seq.index es' j == Seq.index es j) /\
                   (p >= 0 ==> p <> h /\ HC.lvx (ops tk tv) es m h p /\ HC.in_bucket (ops tk tv) es (bof es i) p /\
                              I32.v (Seq.index es' p).E.fld_Next == h /\ I32.v (Seq.index es p).E.fld_Next == i))
  = if p >= 0 then begin
      pred_live bs es m h i p q;
      assert (Seq.index bs' (bof es i) == Seq.index bs (bof es i))
    end

let move_other (#tk #tv: Type0) (bs bs': seq I32.t) (es es': seq (entry tk tv)) (m h i p q: int) (c: option (Eq.comparer tk))
               (b': nat)
  : Lemma (requires wfm bs es m h c /\ 0 <= i /\ i < m /\ i <> h /\ copied es h i /\ move_writes bs bs' es es' m h i p q /\
                    b' < Seq.length bs /\ b' <> bof es i)
          (ensures HC.bucket_ok (ops tk tv) bs' es' m i b')
  = reveal_opaque (`%wfm_core) (wfm_core #tk #tv);
    let o = ops tk tv in
    move_facts bs bs' es es' m h i p q c;
    in_bucket_bof es i;
    assert (HC.bucket_ok o bs es m h b');
    HC.bucket_frame o bs bs' es es' m h m i b'

let move_rest (#tk #tv: Type0) (bs bs': seq I32.t) (es es': seq (entry tk tv)) (m h i p q: int) (c: option (Eq.comparer tk))
  : Lemma (requires wfm bs es m h c /\ 0 <= i /\ i < m /\ i <> h /\ copied es h i /\ move_writes bs bs' es es' m h i p q)
          (ensures (forall (j: nat). j < m /\ j < Seq.length es' /\ j <> i ==> I32.v (Seq.index es' j).E.fld_Next >= -1) /\
                   HC.hashes_ok (ops tk tv) (eff c) es' m i)
  = reveal_opaque (`%wfm_core) (wfm_core #tk #tv);
    let o = ops tk tv in
    move_facts bs bs' es es' m h i p q c;
    assert (HC.lvx o es m h i);
    let hs (j: int) : Lemma (HC.lvx o es' m i j ==> o.HC.hc (Seq.index es' j) == HC.hv (eff c) (o.HC.key (Seq.index es' j))) =
      if HC.lvx o es' m i j then begin
        if j = h then () else if j = p then () else assert (HC.lvx o es m h j)
      end
    in
    FStar.Classical.forall_intro hs

let move_keys (#tk #tv: Type0) (es es': seq (entry tk tv)) (m h i: int)
  : Lemma (requires 0 <= h /\ h < m /\ 0 <= i /\ i < m /\ m <= Seq.length es /\ (i == h + 1 \/ i == h - 1) /\
                    copied es h i /\ same_data es es')
          (ensures keysh es' m i == keysh es m h /\ valuesh es' m i == valuesh es m h)
  = assert (Seq.equal (keysh es' m i) (keysh es m h));
    assert (Seq.equal (valuesh es' m i) (valuesh es m h))

/// `UpdateBucketIndex(i, h - i)` moves the hole from `h` to `i`.
let move_ok (#tk #tv: Type0) (bs bs': seq I32.t) (es es': seq (entry tk tv)) (m h i p q: int) (c: option (Eq.comparer tk))
  : Lemma (requires wfm bs es m h c /\ 0 <= i /\ i < m /\ (i == h + 1 \/ i == h - 1) /\ copied es h i /\
                    move_writes bs bs' es es' m h i p q)
          (ensures wfm bs' es' m i c /\ keysh es' m i == keysh es m h /\ valuesh es' m i == valuesh es m h)
  = move_facts bs bs' es es' m h i p q c;
    move_bucket bs bs' es es' m h i p q c;
    let ob (b': nat) : Lemma (b' < Seq.length bs' ==> HC.bucket_ok (ops tk tv) bs' es' m i b') =
      if b' < Seq.length bs' && b' <> bof es i then move_other bs bs' es es' m h i p q c b'
    in
    FStar.Classical.forall_intro ob;
    assert (HC.chains (ops tk tv) bs' es' m i);
    move_rest bs bs' es es' m h i p q c;
    move_keys es es' m h i;
    reveal_opaque (`%wfm_core) (wfm_core #tk #tv)

/// The searches start at the head of the chain.
let wf_pred_start (#tk #tv: Type0) (bs: seq I32.t) (es: seq (entry tk tv)) (n x: int) (c: option (Eq.comparer tk))
  : Lemma (requires wf bs es n c /\ 0 <= x /\ x < n /\ x < Seq.length es /\ Seq.length bs == Seq.length es /\
                    I32.v (Seq.index bs (bof es x)) <> x + 1)
          (ensures pred bs es n (-1) x (head bs es x) 0)
  = wf_keys bs es n c;
    reveal_opaque (`%wf) (wf #tk #tv);
    pred_start bs es n (-1) x

let wfm_pred_start (#tk #tv: Type0) (bs: seq I32.t) (es: seq (entry tk tv)) (m h x: int) (c: option (Eq.comparer tk))
  : Lemma (requires wfm bs es m h c /\ 0 <= x /\ x < m /\ x <> h /\ I32.v (Seq.index bs (bof es x)) <> x + 1)
          (ensures pred bs es m h x (head bs es x) 0)
  = reveal_opaque (`%wfm_core) (wfm_core #tk #tv);
    pred_start bs es m h x

(* ---------------------------------------------------------------------------------- *)
(* Unlinking an entry (RemoveEntryFromBucket) *)

/// A pair's link is the end of its chain or an entry.
#push-options "--fuel 1 --ifuel 1"
let wf_next (#tk #tv: Type0) (bs: seq I32.t) (es: seq (entry tk tv)) (n x: int) (c: option (Eq.comparer tk))
  : Lemma (requires wf bs es n c /\ 0 <= x /\ x < n)
          (ensures x < Seq.length es /\ -1 <= I32.v (Seq.index es x).E.fld_Next /\
                   I32.v (Seq.index es x).E.fld_Next < Seq.length es)
  = wf_keys bs es n c;
    reveal_opaque (`%wf) (wf #tk #tv);
    let o = ops tk tv in
    assert (HC.lvx o es n (-1) x);
    let (l, qt) = find_in_chain bs es n (-1) x in
    assert (HC.walk o es (head bs es x) (qt + 1) == HC.nxt o es x);
    if qt + 1 < l then HC.chain_live o es n (-1) (bof es x) (head bs es x) l (qt + 1)
#pop-options

/// The changes `RemoveEntryFromBucket(x)` makes: the head of `x`'s bucket, or the link of
/// its predecessor `p`, now skips `x`.
let unlink_writes (#tk #tv: Type0) (bs bs': seq I32.t) (es es': seq (entry tk tv)) (n x p q: int) : prop =
  Seq.length es > 0 /\ Seq.length bs == Seq.length es /\
  Seq.length es' == Seq.length es /\ Seq.length bs' == Seq.length bs /\
  0 <= x /\ x < Seq.length es /\
  (if p < 0
   then I32.v (Seq.index bs (bof es x)) == x + 1 /\ es' == es /\
        same_but bs bs' (bof es x) /\ I32.v (Seq.index bs' (bof es x)) == I32.v (Seq.index es x).E.fld_Next + 1
   else pred bs es n (-1) x p q /\ p < Seq.length es /\ I32.v (Seq.index es p).E.fld_Next == x /\ bs' == bs /\
        (forall (j: nat). {:pattern Seq.index es' j} j < Seq.length es /\ j <> p ==> Seq.index es' j == Seq.index es j) /\
        (Seq.index es' p).E.fld_Next == (Seq.index es x).E.fld_Next /\
        (Seq.index es' p).E.fld_HashCode == (Seq.index es p).E.fld_HashCode /\
        (Seq.index es' p).E.fld_Key == (Seq.index es p).E.fld_Key /\
        (Seq.index es' p).E.fld_Value == (Seq.index es p).E.fld_Value)

#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
let unlink_chains (#tk #tv: Type0) (bs bs': seq I32.t) (es es': seq (entry tk tv)) (n x p q: int) (c: option (Eq.comparer tk))
  : Lemma (requires wf bs es n c /\ x < n /\ unlink_writes bs bs' es es' n x p q)
          (ensures HC.chains (ops tk tv) bs' es' n x /\ same_data es es' /\
                   (p >= 0 ==> HC.lvx (ops tk tv) es n (-1) p))
  = wf_keys bs es n c;
    reveal_opaque (`%wf) (wf #tk #tv);
    let o = ops tk tv in
    let b = bof es x in
    let hd = head bs es x in
    in_bucket_bof es x;
    assert (HC.lvx o es n (-1) x);
    let (l, qt) = find_in_chain bs es n (-1) x in
    if p < 0 then begin
      if qt > 0 then HC.chain_distinct o es n (-1) b hd l 0 qt;
      assert (qt == 0);
      HC.chains_unlink o bs bs' es es' n b l qt x
    end else begin
      pred_live bs es n (-1) x p q;
      pred_pos bs es n (-1) x p q l;
      if qt <> q + 1 then HC.chain_distinct o es n (-1) b hd l (if qt < q + 1 then qt else q + 1) (if qt < q + 1 then q + 1 else qt);
      assert (qt == q + 1);
      assert (HC.prev o es hd qt == p);
      assert (forall (j: int). j <> x ==> HC.lvx o es' n x j == HC.lvx o es n (-1) j);
      HC.chains_unlink o bs bs' es es' n b l qt x
    end
#pop-options

/// `RemoveEntryFromBucket(x)` leaves `x` the hole.
let unlink_ok (#tk #tv: Type0) (bs bs': seq I32.t) (es es': seq (entry tk tv)) (n x p q: int) (c: option (Eq.comparer tk))
  : Lemma (requires wf bs es n c /\ x < n /\ unlink_writes bs bs' es es' n x p q)
          (ensures wfm bs' es' n x c /\ keysh es' n x == keysh es n x /\ valuesh es' n x == valuesh es n x)
  = unlink_chains bs bs' es es' n x p q c;
    wf_keys bs es n c;
    reveal_opaque (`%wf) (wf #tk #tv);
    let o = ops tk tv in
    let hs (j: int) : Lemma (HC.lvx o es' n x j ==> o.HC.hc (Seq.index es' j) == HC.hv (eff c) (o.HC.key (Seq.index es' j))) =
      if HC.lvx o es' n x j then assert (HC.lvx o es n (-1) j)
    in
    FStar.Classical.forall_intro hs;
    reveal_opaque (`%wfm_core) (wfm_core #tk #tv);
    assert (Seq.equal (keysh es' n x) (keysh es n x));
    assert (Seq.equal (valuesh es' n x) (valuesh es n x))

(* ---------------------------------------------------------------------------------- *)
(* Filling the hole (PushEntryIntoBucket) *)

/// `s` with `x` inserted at `i`; `s` without its `i`th element.
let ins (#a: Type) (s: seq a) (i: int) (x: a) : seq a =
  if 0 <= i && i <= Seq.length s then Seq.append (Seq.snoc (Seq.slice s 0 i) x) (Seq.slice s i (Seq.length s)) else s

let del (#a: Type) (s: seq a) (i: int) : seq a =
  if 0 <= i && i < Seq.length s then Seq.append (Seq.slice s 0 i) (Seq.slice s (i + 1) (Seq.length s)) else s

/// The bucket an entry's stored hash code selects, in a table of `len` buckets.
let bk (#tk #tv: Type0) (y: entry tk tv) (len: pos) : nat = U32.v y.E.fld_HashCode % len

let wfm_head (#tk #tv: Type0) (bs: seq I32.t) (es: seq (entry tk tv)) (m h: int) (c: option (Eq.comparer tk)) (b: int)
  : Lemma (requires wfm bs es m h c /\ 0 <= b /\ b < Seq.length bs)
          (ensures 0 <= I32.v (Seq.index bs b) /\ I32.v (Seq.index bs b) <= Seq.length es)
  = reveal_opaque (`%wfm_core) (wfm_core #tk #tv);
    assert (HC.bucket_ok (ops tk tv) bs es m h b);
    let o = ops tk tv in
    let hd = I32.v (Seq.index bs b) - 1 in
    let l = FStar.IndefiniteDescription.indefinite_description_ghost nat
              (fun l -> HC.chain_at o es m h b hd l /\ HC.complete_at o es m h b hd l) in
    if l > 0 then assert (HC.lvx o es m h (HC.walk o es hd 0))
    else assert (HC.walk o es hd 0 == -1)

let fill_keys (#tk #tv: Type0) (es: seq (entry tk tv)) (m h: int) (y: entry tk tv)
  : Lemma (requires 0 <= h /\ h < m /\ m <= Seq.length es)
          (ensures keys (Seq.upd es h y) m == ins (keysh es m h) h y.E.fld_Key /\
                   values (Seq.upd es h y) m == ins (valuesh es m h) h y.E.fld_Value)
  = let es' = Seq.upd es h y in
    let k = keysh es m h in
    let v = valuesh es m h in
    let r = ins k h y.E.fld_Key in
    let rv = ins v h y.E.fld_Value in
    assert (Seq.length r == m /\ Seq.length rv == m);
    let one (j: nat{j < m}) : Lemma (Seq.index (keys es' m) j == Seq.index r j /\ Seq.index (values es' m) j == Seq.index rv j) =
      if j < h then ()
      else if j = h then ()
      else assert (skip1 h (j - 1) == j)
    in
    FStar.Classical.forall_intro one;
    assert (Seq.equal (keys es' m) r);
    assert (Seq.equal (values es' m) rv)

#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
let fill_chains (#tk #tv: Type0) (bs bs': seq I32.t) (es: seq (entry tk tv)) (m h: int) (c: option (Eq.comparer tk))
                (y: entry tk tv)
  : Lemma (requires wfm bs es m h c /\
                    I32.v y.E.fld_Next == I32.v (Seq.index bs (bk y (Seq.length es))) - 1 /\
                    same_but bs bs' (bk y (Seq.length es)) /\ I32.v (Seq.index bs' (bk y (Seq.length es))) == h + 1)
          (ensures HC.chains (ops tk tv) bs' (Seq.upd es h y) m (-1))
  = let o = ops tk tv in
    let es' = Seq.upd es h y in
    let b = bk y (Seq.length es) in
    wfm_head bs es m h c b;
    reveal_opaque (`%wfm_core) (wfm_core #tk #tv);
    bkt_sx y.E.fld_HashCode (Seq.length es);
    assert (HC.bkt (o.HC.hc (Seq.index es' h)) (Seq.length es) == b);
    assert (forall (j: int). HC.lvx o es' m (-1) j == (HC.lvx o es m h j || j = h));
    HC.chains_link o bs bs' es es' m h m (-1) h
#pop-options

let fill_ok (#tk #tv: Type0) (bs bs': seq I32.t) (es: seq (entry tk tv)) (m h: int) (c: option (Eq.comparer tk))
            (y: entry tk tv)
  : Lemma (requires wfm bs es m h c /\
                    I32.v y.E.fld_Next == I32.v (Seq.index bs (bk y (Seq.length es))) - 1 /\
                    sx y.E.fld_HashCode == HC.hv (eff c) y.E.fld_Key /\
                    same_but bs bs' (bk y (Seq.length es)) /\ I32.v (Seq.index bs' (bk y (Seq.length es))) == h + 1)
          (ensures wf bs' (Seq.upd es h y) m c /\
                   keys (Seq.upd es h y) m == ins (keysh es m h) h y.E.fld_Key /\
                   values (Seq.upd es h y) m == ins (valuesh es m h) h y.E.fld_Value)
  = let o = ops tk tv in
    let es' = Seq.upd es h y in
    fill_chains bs bs' es m h c y;
    wfm_head bs es m h c (bk y (Seq.length es));
    reveal_opaque (`%wfm_core) (wfm_core #tk #tv);
    ndead_zero es' m (-1);
    let hs (j: int) : Lemma (HC.lvx o es' m (-1) j ==> o.HC.hc (Seq.index es' j) == HC.hv (eff c) (o.HC.key (Seq.index es' j))) =
      if HC.lvx o es' m (-1) j && j <> h then assert (HC.lvx o es m h j)
    in
    FStar.Classical.forall_intro hs;
    reveal_opaque (`%wf) (wf #tk #tv);
    fill_keys es m h y

/// The pairs with a hole, against the pairs: one removed, or one to be inserted.
let keysh_del (#tk #tv: Type0) (es: seq (entry tk tv)) (n x: int)
  : Lemma (requires 0 <= x /\ x < n /\ n <= Seq.length es)
          (ensures keysh es n x == del (keys es n) x /\ valuesh es n x == del (values es n) x)
  = assert (Seq.equal (keysh es n x) (del (keys es n) x));
    assert (Seq.equal (valuesh es n x) (del (values es n) x))

let ins_del (#a: Type) (s: seq a) (i: int) (x: a)
  : Lemma (requires 0 <= i /\ i < Seq.length s)
          (ensures ins (del s i) i x == Seq.upd s i x)
  = assert (Seq.equal (ins (del s i) i x) (Seq.upd s i x))

(* ---------------------------------------------------------------------------------- *)
(* Rebuilding the chains (Resize) *)

/// A pair's stored hash code is its key's.
let wf_hash (#tk #tv: Type0) (bs: seq I32.t) (es: seq (entry tk tv)) (n j: int) (c: option (Eq.comparer tk))
  : Lemma (requires wf bs es n c /\ 0 <= j /\ j < n)
          (ensures j < Seq.length es /\ sx (Seq.index es j).E.fld_HashCode == HC.hv (eff c) (Seq.index es j).E.fld_Key)
  = wf_keys bs es n c;
    reveal_opaque (`%wf) (wf #tk #tv);
    assert (HC.lvx (ops tk tv) es n (-1) j)

/// `PushEntryIntoBucket(ref newEntries[i], i)`: one more entry in the chains.
let push_ok (#tk #tv: Type0) (bs bs': seq I32.t) (es: seq (entry tk tv)) (i: int) (c: option (Eq.comparer tk))
            (y: entry tk tv)
  : Lemma (requires 0 <= i /\ i < Seq.length es /\ wf bs es i c /\ Seq.length bs == Seq.length es /\
                    I32.v y.E.fld_Next == I32.v (Seq.index bs (bk y (Seq.length es))) - 1 /\
                    sx y.E.fld_HashCode == HC.hv (eff c) y.E.fld_Key /\
                    same_but bs bs' (bk y (Seq.length es)) /\ I32.v (Seq.index bs' (bk y (Seq.length es))) == i + 1)
          (ensures wf bs' (Seq.upd es i y) (i + 1) c)
  = open_ok bs es i c;
    fill_ok bs bs' es (i + 1) i c y

/// The pairs are the keys and values below the count, whatever the links.
let pairs_same (#tk #tv: Type0) (es es': seq (entry tk tv)) (n: int)
  : Lemma (requires 0 <= n /\ n <= Seq.length es /\ n <= Seq.length es' /\
                    (forall (j: nat). {:pattern Seq.index es' j} j < n ==>
                       (Seq.index es' j).E.fld_Key == (Seq.index es j).E.fld_Key /\
                       (Seq.index es' j).E.fld_Value == (Seq.index es j).E.fld_Value))
          (ensures keys es' n == keys es n /\ values es' n == values es n)
  = assert (Seq.equal (keys es' n) (keys es n));
    assert (Seq.equal (values es' n) (values es n))

/// A head is the end of a chain or an entry.
let wf_head (#tk #tv: Type0) (bs: seq I32.t) (es: seq (entry tk tv)) (n: int) (c: option (Eq.comparer tk)) (b: int)
  : Lemma (requires wf bs es n c /\ 0 <= b /\ b < Seq.length bs)
          (ensures 0 <= I32.v (Seq.index bs b) /\ I32.v (Seq.index bs b) <= Seq.length es)
  = reveal_opaque (`%wf) (wf #tk #tv);
    assert (HC.bucket_ok (ops tk tv) bs es n (-1) b);
    let o = ops tk tv in
    let hd = I32.v (Seq.index bs b) - 1 in
    let l = FStar.IndefiniteDescription.indefinite_description_ghost nat
              (fun l -> HC.chain_at o es n (-1) b hd l /\ HC.complete_at o es n (-1) b hd l) in
    if l > 0 then assert (HC.lvx o es n (-1) (HC.walk o es hd 0))
    else assert (HC.walk o es hd 0 == -1)

/// Below `n`, `es` holds `old`'s pairs and hash codes (whatever the links).
let same_kvh (#tk #tv: Type0) (es old: seq (entry tk tv)) (n: int) : prop =
  0 <= n /\ n <= Seq.length es /\ n <= Seq.length old /\
  (forall (j: nat). {:pattern Seq.index es j} j < n ==>
     (Seq.index es j).E.fld_Key == (Seq.index old j).E.fld_Key /\
     (Seq.index es j).E.fld_Value == (Seq.index old j).E.fld_Value /\
     (Seq.index es j).E.fld_HashCode == (Seq.index old j).E.fld_HashCode)

/// `Array.Copy(_entries, newEntries, count)`.
let same_kvh_copy (#tk #tv: Type0) (es old: seq (entry tk tv)) (n: int)
  : Lemma (requires 0 <= n /\ n <= Seq.length es /\ n <= Seq.length old /\ Seq.slice es 0 n == Seq.slice old 0 n)
          (ensures same_kvh es old n)
  = let aux (j: nat) : Lemma (j < n ==> Seq.index es j == Seq.index old j) =
      if j < n then (assert (Seq.index (Seq.slice es 0 n) j == Seq.index es j);
                     assert (Seq.index (Seq.slice old 0 n) j == Seq.index old j))
    in
    FStar.Classical.forall_intro aux

/// What `PushEntryIntoBucket(ref es[i], i)` changes.
let push_writes (#tk #tv: Type0) (bs bs': seq I32.t) (es es': seq (entry tk tv)) (i: int) : prop =
  0 <= i /\ i < Seq.length es /\ Seq.length bs == Seq.length es /\ Seq.length es' == Seq.length es /\
  (let x = Seq.index es i in
   let y = Seq.index es' i in
   let b = bk x (Seq.length es) in
   y.E.fld_Key == x.E.fld_Key /\ y.E.fld_Value == x.E.fld_Value /\ y.E.fld_HashCode == x.E.fld_HashCode /\
   I32.v y.E.fld_Next == I32.v (Seq.index bs b) - 1 /\
   same_but bs bs' b /\ I32.v (Seq.index bs' b) == i + 1) /\
  es' == Seq.upd es i (Seq.index es' i)

/// One more step of `Resize`'s loop.
let push_step (#tk #tv: Type0) (bs bs': seq I32.t) (es es': seq (entry tk tv)) (ob: seq I32.t) (old: seq (entry tk tv))
              (i n: int) (c: option (Eq.comparer tk))
  : Lemma (requires wf bs es i c /\ wf ob old n c /\ 0 <= i /\ i < n /\ same_kvh es old n /\ push_writes bs bs' es es' i)
          (ensures wf bs' es' (i + 1) c /\ same_kvh es' old n)
  = wf_hash ob old n i c;
    push_ok bs bs' es i c (Seq.index es' i)

/// `Resize` keeps the pairs.
let resize_pairs (#tk #tv: Type0) (es old: seq (entry tk tv)) (n: int)
  : Lemma (requires same_kvh es old n)
          (ensures keys es n == keys old n /\ values es n == values old n)
  = pairs_same old es n

(* ---------------------------------------------------------------------------------- *)
(* Callers: `TryInsert`, `RemoveAt`, `SetAt` *)

/// `es2` is `es` but at `h`: writes into the hole.
let same_off (#tk #tv: Type0) (es es2: seq (entry tk tv)) (h: int) : prop =
  Seq.length es2 == Seq.length es /\
  (forall (j: nat). j < Seq.length es /\ j <> h ==> Seq.index es2 j == Seq.index es j)

let hole_eq (#tk #tv: Type0) (bs: seq I32.t) (es es2: seq (entry tk tv)) (m h: int) (c: option (Eq.comparer tk))
  : Lemma (requires wfm bs es m h c /\ same_off es es2 h)
          (ensures wfm bs es2 m h c /\ keysh es2 m h == keysh es m h /\ valuesh es2 m h == valuesh es m h /\
                   Seq.length es2 == Seq.length es)
  = assert (Seq.equal es2 (Seq.upd es h (Seq.index es2 h)));
    hole_set bs es m h c (Seq.index es2 h)

/// `PushEntryIntoBucket(ref es[h], h)` fills the hole with the entry written there.
let fill_step (#tk #tv: Type0) (bs bs': seq I32.t) (es es': seq (entry tk tv)) (m h: int) (c: option (Eq.comparer tk))
  : Lemma (requires wfm bs es m h c /\ push_writes bs bs' es es' h /\
                    U32.v (Seq.index es h).E.fld_HashCode == hash_of c (Seq.index es h).E.fld_Key)
          (ensures wf bs' es' m c /\ Seq.length es' == Seq.length es /\ Seq.length bs' == Seq.length bs /\
                   keys es' m == ins (keysh es m h) h (Seq.index es h).E.fld_Key /\
                   values es' m == ins (valuesh es m h) h (Seq.index es h).E.fld_Value)
  = let y = Seq.index es' h in
    sx_hash y.E.fld_HashCode (Eq.hash (eff c) y.E.fld_Key);
    fill_ok bs bs' es m h c y

let open_ok' (#tk #tv: Type0) (bs: seq I32.t) (es: seq (entry tk tv)) (n: int) (c: option (Eq.comparer tk))
  : Lemma (requires wf bs es n c /\ 0 <= n /\ n < Seq.length es /\ Seq.length bs == Seq.length es)
          (ensures wfm bs es (n + 1) n c /\ keysh es (n + 1) n == keys es n /\ valuesh es (n + 1) n == values es n)
  = open_ok bs es n c

let close_ok' (#tk #tv: Type0) (bs: seq I32.t) (es es2: seq (entry tk tv)) (n: int) (c: option (Eq.comparer tk))
  : Lemma (requires wfm bs es n (n - 1) c /\ same_off es es2 (n - 1))
          (ensures wf bs es2 (n - 1) c /\ keys es2 (n - 1) == keysh es n (n - 1) /\ values es2 (n - 1) == valuesh es n (n - 1))
  = assert (Seq.equal es2 (Seq.upd es (n - 1) (Seq.index es2 (n - 1))));
    close_ok bs es n c (Seq.index es2 (n - 1))

let keysh_del' (#tk #tv: Type0) (es: seq (entry tk tv)) (n x: int)
  : Lemma (requires 0 <= x /\ x < n /\ n <= Seq.length es)
          (ensures keysh es n x == del (keys es n) x /\ valuesh es n x == del (values es n) x /\
                   Seq.length (keys es n) == n /\ Seq.length (values es n) == n)
  = keysh_del es n x
