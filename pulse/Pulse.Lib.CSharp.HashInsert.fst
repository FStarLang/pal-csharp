module Pulse.Lib.CSharp.HashInsert

/// Growing and filling the separate-chaining table of `Pulse.Lib.CSharp.HashChain`
/// (doc/translation.md §30): inserting an entry (from the free list or at the end),
/// rebuilding the chains into new arrays (`Resize`), recomputing the hash codes
/// (`Resize(.., forceNewHashCodes: true)`), and compacting into new arrays (`CopyEntries`).
///
/// Everything here is proved. The collection's view is any projection `f` of the entries
/// (`view o f`): the key for `HashSet<T>`, the key-value pair for `Dictionary<TKey,TValue>`.

open FStar.Seq
module Seq = FStar.Seq
module Eq = Pulse.Lib.CSharp.Equality
module I32 = FStar.Int32
open Pulse.Lib.CSharp.HashChain

/// The table `o` seen through the projection `f`: same links, other items.
let view (#e #k #a: Type0) (o: ops e k) (f: e -> a) : ops e a = { hc = o.hc; nx = o.nx; key = f }

let rec items_len_view (#e #k #a: Type0) (o: ops e k) (f: e -> a) (es: seq e) (n: nat{n <= Seq.length es}) (h: int)
  : Lemma (ensures Seq.length (items (view o f) es n h) == Seq.length (items o es n h) /\
                   ndead (view o f) es n h == ndead o es n h)
          (decreases n)
          [SMTPat (items (view o f) es n h)]
  = if n = 0 then () else items_len_view o f es (n - 1) h

let pos_view (#e #k #a: Type0) (o: ops e k) (f: e -> a) (es: seq e) (j: nat{j <= Seq.length es})
  : Lemma (pos (view o f) es j == pos o es j)
  = items_len_view o f es j (-1)

let rec items_view_key (#e #k: Type0) (o: ops e k) (es: seq e) (n: nat{n <= Seq.length es}) (h: int)
  : Lemma (ensures items (view o o.key) es n h == items o es n h) (decreases n)
  = if n = 0 then () else items_view_key o es (n - 1) h

let rec items_mono (#e #k: Type0) (o: ops e k) (es: seq e) (i: nat) (n: nat{i <= n /\ n <= Seq.length es})
  : Lemma (ensures Seq.length (items o es i (-1)) <= Seq.length (items o es n (-1))) (decreases n)
  = if i = n then () else items_mono o es i (n - 1)

(* ---------------------------------------------------------------------------------- *)
(* Facts about a well-formed table *)

/// A bucket holds 0 or a 1-based index in range.
let bucket_range (#e #k: Type0) (o: ops e k) (bs: seq I32.t) (es: seq e) (m hole: int) (b: nat)
  : Lemma (requires chains o bs es m hole /\ b < Seq.length bs)
          (ensures 0 <= I32.v (Seq.index bs b) /\ I32.v (Seq.index bs b) <= Seq.length es)
  = assert (bucket_ok o bs es m hole b);
    let h = I32.v (Seq.index bs b) - 1 in
    let l = FStar.IndefiniteDescription.indefinite_description_ghost nat
              (fun l -> chain_at o es m hole b h l /\ complete_at o es m hole b h l) in
    if l = 0 then assert (walk o es h 0 == h) else assert (lvx o es m hole (walk o es h 0))

/// No entry is a chain node: every bucket is empty.
let chains_none (#e #k: Type0) (o: ops e k) (bs: seq I32.t) (es: seq e)
  : Lemma (requires Seq.length bs == Seq.length es /\
                    (forall (b: nat). b < Seq.length bs ==> I32.v (Seq.index bs b) == 0))
          (ensures chains o bs es 0 (-1))
  = let one (b: nat) : Lemma (b < Seq.length bs ==> bucket_ok o bs es 0 (-1) b) =
      if b < Seq.length bs then assert (chain_at o es 0 (-1) b (-1) 0 /\ complete_at o es 0 (-1) b (-1) 0)
    in
    FStar.Classical.forall_intro one

(* ---------------------------------------------------------------------------------- *)
(* Inserting (AddIfNotPresent, TryInsert) *)

/// The entry `idx` is filled in with `x`, whose hash at `c` is stored, linked at the head
/// of `x`'s bucket: `entry.HashCode = hashCode; entry.Next = bucket - 1; entry.Value = x;
/// bucket = index + 1`. Every other entry and bucket is unchanged.
let insert_writes (#e #k: Type0) (o: ops e k) (c: Eq.handle) (bs bs': seq I32.t) (es es': seq e)
                  (x: k) (idx: int)
  : prop
  = Seq.length es > 0 /\ Seq.length bs == Seq.length es /\
    Seq.length es' == Seq.length es /\ inr es idx /\
    (forall (j: nat). {:pattern Seq.index es' j} j < Seq.length es /\ j <> idx ==> Seq.index es' j == Seq.index es j) /\
    (let b = bkt (hv c x) (Seq.length es) in
     o.hc (Seq.index es' idx) == hv c x /\ o.key (Seq.index es' idx) == x /\
     o.nx (Seq.index es' idx) == I32.v (Seq.index bs b) - 1 /\
     same_but bs bs' b /\ I32.v (Seq.index bs' b) == idx + 1)

/// Where the insertion goes: the head of the free list, or the end.
let insert_slot (#e #k: Type0) (o: ops e k) (es: seq e) (n fl fc idx n' fl' fc': int) : prop =
  (fc > 0 /\ idx == fl /\ n' == n /\ fl' == fnxt o es fl /\ fc' == fc - 1) \/
  (fc == 0 /\ idx == n /\ n' == n + 1 /\ fl' == fl /\ fc' == fc)

/// What the code reads before it writes: the bucket of `x`, and the free list's head and
/// link, are in range.
let insert_pre (#e #k: Type0) (o: ops e k) (c: Eq.handle) (bs: seq I32.t) (es: seq e) (n fl fc: int) (x: k)
  : Lemma (requires wf o c bs es n fl fc /\ Seq.length es > 0)
          (ensures 0 <= I32.v (Seq.index bs (bkt (hv c x) (Seq.length es))) /\
                   I32.v (Seq.index bs (bkt (hv c x) (Seq.length es))) <= Seq.length es /\
                   (fc > 0 ==> 0 <= fl /\ fl < n /\ -1 <= fnxt o es fl /\ fnxt o es fl < n) /\
                   (fc == 0 ==> fl == -1) /\ fc <= n)
  = bucket_range o bs es n (-1) (bkt (hv c x) (Seq.length es));
    fl_range o es n (-1) fl fc;
    count_items o es n (-1);
    if fc > 0 then begin
      free_pop o es n fl fc;
      if fc > 1 then assert (fwalk o es fl 1 == fnxt o es fl);
      if fc > 1 then assert (dead o es n fl (fwalk o es fl 1))
      else assert (fwalk o es fl 1 == fnxt o es fl)
    end

#push-options "--z3rlimit 60 --fuel 1 --ifuel 1"
let insert_ok (#e #k #a: Type0) (o: ops e k) (f: e -> a) (c: Eq.handle) (bs bs': seq I32.t) (es es': seq e)
              (n fl fc: int) (x: k) (idx n' fl' fc': int)
  : Lemma (requires wf o c bs es n fl fc /\ insert_writes o c bs bs' es es' x idx /\
                    insert_slot o es n fl fc idx n' fl' fc')
          (ensures 0 <= idx /\ idx < n' /\ n' <= Seq.length es /\
                   pos o es idx <= Seq.length (items o es n (-1)) /\
                   wf o c bs' es' n' fl' fc' /\
                   items o es' n' (-1) == insert_at (items o es n (-1)) (pos o es idx) x /\
                   items (view o f) es' n' (-1) ==
                     insert_at (items (view o f) es n (-1)) (pos o es idx) (f (Seq.index es' idx)))
  = let len = Seq.length es in
    let b = bkt (hv c x) len in
    let v = view o f in
    bucket_range o bs es n (-1) b;
    fl_range o es n (-1) fl fc;
    items_view_key o es n (-1);
    items_len_view o f es idx (-1);
    let fr (j: nat) : Lemma (j < idx ==> Seq.index es' j == Seq.index es j) = () in
    FStar.Classical.forall_intro fr;
    items_frame o es es' idx (-1);
    items_frame v es es' idx (-1);
    items_mono o es idx n;
    if fc > 0 then begin
      free_pop o es n fl fc;
      assert (forall (j: int). lvx o es' n (-1) j == (lvx o es n (-1) j || j = idx));
      chains_link o bs bs' es es' n (-1) n (-1) idx;
      // the free list, with `idx` taken off it
      items_frame o es es' n idx;
      items_frame v es es' n idx;
      items_hole o es n idx;
      items_hole o es' n idx;
      items_hole v es n idx;
      items_hole v es' n idx;
      assert (forall (j: int). dead o es n idx j == dead o es' n (-1) j);
      free_same o es es' n idx (-1) (fnxt o es fl) (fc - 1);
      items_len_view o f es' idx (-1)
    end else begin
      assert (fl == -1);
      assert (idx == n /\ n < len);
      assert (forall (j: int). lvx o es' (n + 1) (-1) j == (lvx o es n (-1) j || j = idx));
      chains_link o bs bs' es es' n (-1) (n + 1) (-1) idx;
      items_frame o es es' n (-1);
      items_frame v es es' n (-1);
      count_items o es n (-1);
      assert (ndead o es' (n + 1) (-1) == 0);
      assert (fwalk o es' fl 0 == -1);
      insert_at_end (items o es n (-1)) x;
      insert_at_end (items v es n (-1)) (f (Seq.index es' idx));
      items_len_view o f es n (-1)
    end
#pop-options

(* ---------------------------------------------------------------------------------- *)
(* Overwriting a value (Dictionary's TryInsert, OverwriteExisting) *)

let rec items_upd (#e #k: Type0) (o: ops e k) (es es': seq e) (n: nat) (j: nat)
  : Lemma (requires n <= Seq.length es /\ Seq.length es' == Seq.length es /\ j < n /\
                    o.nx (Seq.index es j) >= -1 /\
                    (forall (i: nat). i < Seq.length es /\ i <> j ==> Seq.index es' i == Seq.index es i) /\
                    o.nx (Seq.index es' j) == o.nx (Seq.index es j))
          (ensures pos o es j < Seq.length (items o es n (-1)) /\
                   items o es' n (-1) == Seq.upd (items o es n (-1)) (pos o es j) (o.key (Seq.index es' j)))
          (decreases n)
  = if n = j + 1 then begin
      items_frame o es es' j (-1);
      assert (Seq.equal (items o es' n (-1)) (Seq.upd (items o es n (-1)) (pos o es j) (o.key (Seq.index es' j))))
    end else begin
      items_upd o es es' (n - 1) j;
      items_index o es (n - 1) j;
      if o.nx (Seq.index es (n - 1)) >= -1 then
        assert (Seq.equal (items o es' n (-1)) (Seq.upd (items o es n (-1)) (pos o es j) (o.key (Seq.index es' j))))
    end

/// Writing anything but the link, hash code and key of a live entry keeps the table.
let overwrite_ok (#e #k #a: Type0) (o: ops e k) (f: e -> a) (c: Eq.handle) (bs: seq I32.t) (es es': seq e)
                 (n fl fc: int) (j: int)
  : Lemma (requires wf o c bs es n fl fc /\ lvx o es n (-1) j /\ Seq.length es' == Seq.length es /\
                    (forall (i: nat). i < Seq.length es /\ i <> j ==> Seq.index es' i == Seq.index es i) /\
                    o.nx (Seq.index es' j) == o.nx (Seq.index es j) /\
                    o.hc (Seq.index es' j) == o.hc (Seq.index es j) /\
                    o.key (Seq.index es' j) == o.key (Seq.index es j))
          (ensures wf o c bs es' n fl fc /\ items o es' n (-1) == items o es n (-1) /\
                   pos o es j < Seq.length (items (view o f) es n (-1)) /\
                   items (view o f) es' n (-1) == Seq.upd (items (view o f) es n (-1)) (pos o es j) (f (Seq.index es' j)))
  = assert (forall (i: int). lvx o es n (-1) i == lvx o es' n (-1) i);
    chains_same o bs es es' n (-1) n (-1);
    items_frame o es es' n (-1);
    assert (forall (i: int). dead o es n (-1) i == dead o es' n (-1) i);
    free_same o es es' n (-1) (-1) fl fc;
    assert (hashes_ok o c es' n (-1));
    items_upd (view o f) es es' n j;
    pos_view o f es j

(* ---------------------------------------------------------------------------------- *)
(* Rebuilding the chains (Resize) *)

/// A table without chains: the free list and the hash codes, over the source entries.
let pre_wf (#e #k: Type0) (o: ops e k) (c: Eq.handle) (es: seq e) (n fl fc: int) : prop =
  0 <= n /\ n <= Seq.length es /\ free_ok o es n (-1) fl fc /\ hashes_ok o c es n (-1)

/// `Array.Copy(_entries, entries, count)` into a new, no shorter, array.
let copy_ok (#e #k #a: Type0) (o: ops e k) (f: e -> a) (c: Eq.handle) (bs: seq I32.t) (old es: seq e) (n fl fc: int)
  : Lemma (requires wf o c bs old n fl fc /\ n <= Seq.length es /\
                    (forall (j: nat). j < n ==> Seq.index es j == Seq.index old j))
          (ensures pre_wf o c es n fl fc /\ items o es n (-1) == items o old n (-1) /\
                   items (view o f) es n (-1) == items (view o f) old n (-1))
  = items_frame o old es n (-1);
    items_frame (view o f) old es n (-1);
    let rec beyond (r: nat) : Lemma (requires r >= fc) (ensures fwalk o old fl r == -1) (decreases r)
      = if r = fc then () else beyond (r - 1)
    in
    let rng (q: nat) : Lemma (fwalk o old fl q == -1 \/ (0 <= fwalk o old fl q /\ fwalk o old fl q < n)) =
      if q < fc then assert (dead o old n (-1) (fwalk o old fl q)) else beyond q
    in
    let fr (q: nat) : Lemma (fwalk o es fl q == fwalk o old fl q) =
      let st (q': nat) : Lemma (fnxt o old (fwalk o old fl q') == fnxt o es (fwalk o old fl q')) = rng q' in
      FStar.Classical.forall_intro st;
      fwalk_frame o old es fl q
    in
    assert (forall (j: int). dead o old n (-1) j == dead o es n (-1) j);
    FStar.Classical.forall_intro fr;
    assert (free_ok o es n (-1) fl fc);
    assert (forall (j: int). lvx o old n (-1) j == lvx o es n (-1) j);
    assert (hashes_ok o c es n (-1))

/// `entry.HashCode = comparer.GetHashCode(entry.Value)` for the live entries below `i`,
/// with the new comparer `c'`: nothing else changes.
let rehashed (#e #k: Type0) (o: ops e k) (c': Eq.handle) (src es: seq e) (n: int) (i: int) : prop =
  0 <= i /\ i <= n /\ n <= Seq.length src /\ Seq.length es == Seq.length src /\
  (forall (j: nat). {:pattern Seq.index es j} j < Seq.length src ==>
     o.nx (Seq.index es j) == o.nx (Seq.index src j) /\ o.key (Seq.index es j) == o.key (Seq.index src j)) /\
  (forall (j: nat). {:pattern Seq.index es j} i <= j /\ j < Seq.length src ==> Seq.index es j == Seq.index src j) /\
  (forall (j: nat). {:pattern Seq.index es j} j < i /\ o.nx (Seq.index es j) >= -1 ==>
     o.hc (Seq.index es j) == hv c' (o.key (Seq.index es j)))

let rehash_start (#e #k: Type0) (o: ops e k) (c': Eq.handle) (src: seq e) (n: int)
  : Lemma (requires 0 <= n /\ n <= Seq.length src) (ensures rehashed o c' src src n 0)
  = ()

/// The step at entry `i`: rehashed if live, untouched if not.
let rehash_step (#e #k: Type0) (o: ops e k) (c': Eq.handle) (src es es': seq e) (n i: int)
  : Lemma (requires rehashed o c' src es n i /\ i < n /\ Seq.length es' == Seq.length es /\
                    (forall (j: nat). j < Seq.length es /\ j <> i ==> Seq.index es' j == Seq.index es j) /\
                    (if o.nx (Seq.index es i) >= -1
                     then o.nx (Seq.index es' i) == o.nx (Seq.index es i) /\
                          o.key (Seq.index es' i) == o.key (Seq.index es i) /\
                          o.hc (Seq.index es' i) == hv c' (o.key (Seq.index es i))
                     else Seq.index es' i == Seq.index es i))
          (ensures rehashed o c' src es' n (i + 1))
  = ()

let rehash_done (#e #k #a: Type0) (o: ops e k) (f: e -> a) (c c': Eq.handle) (src es: seq e) (n fl fc: int)
  : Lemma (requires pre_wf o c src n fl fc /\ rehashed o c' src es n n /\
                    (forall (j: nat). j < Seq.length src ==> f (Seq.index es j) == f (Seq.index src j)))
          (ensures pre_wf o c' es n fl fc /\ items o es n (-1) == items o src n (-1) /\
                   items (view o f) es n (-1) == items (view o f) src n (-1))
  = assert (forall (j: int). dead o src n (-1) j == dead o es n (-1) j);
    items_frame o src es n (-1);
    items_frame (view o f) src es n (-1);
    free_same o src es n (-1) (-1) fl fc

/// The rebuild has linked the live entries below `i` into the buckets `bs`; the entries
/// from `i` on are still the source's.
let rebuilt (#e #k: Type0) (o: ops e k) (bs: seq I32.t) (src es: seq e) (n i: int) : prop =
  0 <= i /\ i <= n /\ n <= Seq.length src /\ Seq.length es == Seq.length src /\ Seq.length src > 0 /\
  chains o bs es i (-1) /\
  (forall (j: nat). {:pattern Seq.index es j} j < i ==>
     o.hc (Seq.index es j) == o.hc (Seq.index src j) /\ o.key (Seq.index es j) == o.key (Seq.index src j) /\
     (o.nx (Seq.index es j) >= -1) == (o.nx (Seq.index src j) >= -1) /\
     (o.nx (Seq.index src j) < -1 ==> o.nx (Seq.index es j) == o.nx (Seq.index src j))) /\
  (forall (j: nat). {:pattern Seq.index es j} i <= j /\ j < Seq.length src ==> Seq.index es j == Seq.index src j)

let rebuild_start (#e #k: Type0) (o: ops e k) (bs: seq I32.t) (src: seq e) (n: int)
  : Lemma (requires 0 <= n /\ n <= Seq.length src /\ Seq.length src > 0 /\ Seq.length bs == Seq.length src /\
                    (forall (b: nat). b < Seq.length bs ==> I32.v (Seq.index bs b) == 0))
          (ensures rebuilt o bs src src n 0)
  = chains_none o bs src

/// `entry.Next = bucket - 1; bucket = i + 1` for a live entry `i`; nothing for a dead one.
let link_writes (#e #k: Type0) (o: ops e k) (bs bs': seq I32.t) (es es': seq e) (i: int) : prop =
  inr es i /\ Seq.length es' == Seq.length es /\ Seq.length bs == Seq.length es /\
  (forall (j: nat). {:pattern Seq.index es' j} j < Seq.length es /\ j <> i ==> Seq.index es' j == Seq.index es j) /\
  (if o.nx (Seq.index es i) >= -1
   then (let b = bkt (o.hc (Seq.index es i)) (Seq.length es) in
         o.hc (Seq.index es' i) == o.hc (Seq.index es i) /\ o.key (Seq.index es' i) == o.key (Seq.index es i) /\
         o.nx (Seq.index es' i) == I32.v (Seq.index bs b) - 1 /\
         same_but bs bs' b /\ I32.v (Seq.index bs' b) == i + 1)
   else es' == es /\ bs' == bs)

let rebuild_bucket (#e #k: Type0) (o: ops e k) (bs: seq I32.t) (src es: seq e) (n i: int)
  : Lemma (requires rebuilt o bs src es n i /\ i < n)
          (ensures 0 <= I32.v (Seq.index bs (bkt (o.hc (Seq.index es i)) (Seq.length es))) /\
                   I32.v (Seq.index bs (bkt (o.hc (Seq.index es i)) (Seq.length es))) <= Seq.length es)
  = bucket_range o bs es i (-1) (bkt (o.hc (Seq.index es i)) (Seq.length es))

#push-options "--z3rlimit 40"
let rebuild_step (#e #k: Type0) (o: ops e k) (bs bs': seq I32.t) (src es es': seq e) (n i: int)
  : Lemma (requires rebuilt o bs src es n i /\ i < n /\ link_writes o bs bs' es es' i)
          (ensures rebuilt o bs' src es' n (i + 1))
  = if o.nx (Seq.index es i) >= -1 then begin
      bucket_range o bs es i (-1) (bkt (o.hc (Seq.index es i)) (Seq.length es));
      assert (forall (j: int). lvx o es' (i + 1) (-1) j == (lvx o es i (-1) j || j = i));
      chains_link o bs bs' es es' i (-1) (i + 1) (-1) i
    end else begin
      assert (forall (j: int). lvx o es' (i + 1) (-1) j == lvx o es i (-1) j);
      chains_same o bs es es' i (-1) (i + 1) (-1)
    end
#pop-options

let rebuild_done (#e #k #a: Type0) (o: ops e k) (f: e -> a) (c: Eq.handle) (bs: seq I32.t) (src es: seq e) (n fl fc: int)
  : Lemma (requires pre_wf o c src n fl fc /\ rebuilt o bs src es n n /\
                    (forall (j: nat). j < Seq.length src ==> f (Seq.index es j) == f (Seq.index src j)))
          (ensures wf o c bs es n fl fc /\ items o es n (-1) == items o src n (-1) /\
                   items (view o f) es n (-1) == items (view o f) src n (-1))
  = assert (forall (j: int). dead o src n (-1) j == dead o es n (-1) j);
    assert (forall (j: int). lvx o src n (-1) j == lvx o es n (-1) j);
    items_frame o src es n (-1);
    items_frame (view o f) src es n (-1);
    free_same o src es n (-1) (-1) fl fc

(* ---------------------------------------------------------------------------------- *)
(* Compacting (CopyEntries) *)

/// The live entries of `old` below `i` have been copied, in order and linked, to the
/// first `m` entries of `es`, which are all live.
let compacted (#e #k #a: Type0) (o: ops e k) (f: e -> a) (c: Eq.handle) (bs: seq I32.t) (old es: seq e)
              (n i m: int) : prop =
  0 <= i /\ i <= n /\ n <= Seq.length old /\ Seq.length es > 0 /\ 0 <= m /\ m <= Seq.length es /\
  hashes_ok o c old n (-1) /\
  chains o bs es m (-1) /\ hashes_ok o c es m (-1) /\ ndead o es m (-1) == 0 /\
  m == Seq.length (items o old i (-1)) /\
  items o es m (-1) == items o old i (-1) /\
  items (view o f) es m (-1) == items (view o f) old i (-1)

let compact_start (#e #k #a: Type0) (o: ops e k) (f: e -> a) (c: Eq.handle) (bs: seq I32.t) (old es: seq e) (n: int)
  : Lemma (requires hashes_ok o c old n (-1) /\ 0 <= n /\ n <= Seq.length old /\ Seq.length es > 0 /\
                    Seq.length bs == Seq.length es /\
                    (forall (b: nat). b < Seq.length bs ==> I32.v (Seq.index bs b) == 0))
          (ensures compacted o f c bs old es n 0 0)
  = chains_none o bs es

/// What the step at `old[i]` writes when it is live: it is copied to `es[m]`, linked at
/// the head of its bucket.
let copy_writes (#e #k: Type0) (o: ops e k) (bs bs': seq I32.t) (old es es': seq e) (i m: int) : prop =
  inr old i /\ inr es m /\ Seq.length es' == Seq.length es /\ Seq.length bs == Seq.length es /\
  (forall (j: nat). {:pattern Seq.index es' j} j < Seq.length es /\ j <> m ==> Seq.index es' j == Seq.index es j) /\
  (let b = bkt (o.hc (Seq.index old i)) (Seq.length es) in
   o.hc (Seq.index es' m) == o.hc (Seq.index old i) /\ o.key (Seq.index es' m) == o.key (Seq.index old i) /\
   o.nx (Seq.index es' m) == I32.v (Seq.index bs b) - 1 /\
   same_but bs bs' b /\ I32.v (Seq.index bs' b) == m + 1)

let compact_room (#e #k #a: Type0) (o: ops e k) (f: e -> a) (c: Eq.handle) (bs: seq I32.t) (old es: seq e) (n i m: int)
  : Lemma (requires compacted o f c bs old es n i m /\ i < n /\ o.nx (Seq.index old i) >= -1 /\
                    Seq.length (items o old n (-1)) <= Seq.length es)
          (ensures m < Seq.length es /\ 0 <= m + 1 /\
                   0 <= I32.v (Seq.index bs (bkt (o.hc (Seq.index old i)) (Seq.length es))) /\
                   I32.v (Seq.index bs (bkt (o.hc (Seq.index old i)) (Seq.length es))) <= Seq.length es)
  = items_mono o old (i + 1) n;
    bucket_range o bs es m (-1) (bkt (o.hc (Seq.index old i)) (Seq.length es))

#push-options "--z3rlimit 60"
let compact_step (#e #k #a: Type0) (o: ops e k) (f: e -> a) (c: Eq.handle) (bs bs': seq I32.t) (old es es': seq e)
                 (n i m: int)
  : Lemma (requires compacted o f c bs old es n i m /\ i < n /\
                    (if o.nx (Seq.index old i) >= -1
                     then copy_writes o bs bs' old es es' i m /\ f (Seq.index es' m) == f (Seq.index old i)
                     else es' == es /\ bs' == bs))
          (ensures compacted o f c bs' old es' n (i + 1) (if o.nx (Seq.index old i) >= -1 then m + 1 else m))
  = if o.nx (Seq.index old i) >= -1 then begin
      bucket_range o bs es m (-1) (bkt (o.hc (Seq.index old i)) (Seq.length es));
      assert (lvx o old n (-1) i);
      assert (forall (j: int). lvx o es' (m + 1) (-1) j == (lvx o es m (-1) j || j = m));
      chains_link o bs bs' es es' m (-1) (m + 1) (-1) m;
      items_frame o es es' m (-1);
      items_frame (view o f) es es' m (-1);
      count_items o es m (-1)
    end else ()
#pop-options

let compact_done (#e #k #a: Type0) (o: ops e k) (f: e -> a) (c: Eq.handle) (bs: seq I32.t) (old es: seq e) (n m: int)
  : Lemma (requires compacted o f c bs old es n n m)
          (ensures wf o c bs es m (-1) 0 /\ items o es m (-1) == items o old n (-1) /\
                   items (view o f) es m (-1) == items (view o f) old n (-1))
  = assert (fwalk o es (-1) 0 == -1)
