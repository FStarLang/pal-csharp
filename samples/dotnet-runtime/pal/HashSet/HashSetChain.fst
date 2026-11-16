module HashSetChain

/// The glue between `HashSet<T>`'s representation, as pal-csharp translates it, and the
/// separate-chaining theory in `Pulse.Lib.CSharp.HashChain` (doc/translation.md §24). Every
/// definition here is a definition; nothing is assumed.

open FStar.Seq
module Seq = FStar.Seq
module I32 = FStar.Int32
module HC = Pulse.Lib.CSharp.HashChain
module Eq = Pulse.Lib.CSharp.Equality
module E = Struct_HashSet_Entry

let entry (t: Type0) = E.struct_HashSet_Entry t

/// `Entry.HashCode`, `Entry.Next` and `Entry.Value`.
let ops (t: Type0) : HC.ops (entry t) t = {
  HC.hc = (fun (x: entry t) -> I32.v x.E.fld_HashCode);
  HC.nx = (fun (x: entry t) -> I32.v x.E.fld_Next);
  HC.key = (fun (x: entry t) -> x.E.fld_Value);
}

/// The comparer the set uses: `_comparer`, or `EqualityComparer<T>.Default` when it is
/// null, which the constructors allow only for a value type.
let eff (#t: Type0) (c: option (Eq.comparer t)) : Eq.handle =
  match c with
  | None -> Eq.default_comparer t
  | Some h -> h

let wf (#t: Type0) (bs: seq I32.t) (es: seq (entry t)) (n fl fc: int) (c: option (Eq.comparer t)) : prop =
  HC.wf (ops t) (eff c) bs es n fl fc

let items (#t: Type0) (es: seq (entry t)) (n: int) : seq t =
  if 0 <= n && n <= Seq.length es then HC.items (ops t) es n (-1) else Seq.empty

let mem (#t: Type0) (c: option (Eq.comparer t)) (xs: seq t) (x: t) : prop =
  HC.mem (eff c) xs x

(* ---------------------------------------------------------------------------------- *)
(* FindItemIndex *)

/// The bucket `x` hashes to, at the comparer `c`, as stored (1-based).
let bucket (#t: Type0) (bs: seq I32.t) (es: seq (entry t)) (c: option (Eq.comparer t)) (x: t) : int =
  if Seq.length es > 0 && Seq.length bs = Seq.length es
  then I32.v (Seq.index bs (HC.bkt (HC.hv (eff c) x) (Seq.length es)))
  else 0

/// The search for `x` has followed `q` links of its chain to `i`, passing no hit.
let search (#t: Type0) (bs: seq I32.t) (es: seq (entry t)) (n fl fc: int) (c: option (Eq.comparer t))
           (x: t) (i q: int) : prop =
  q >= 0 /\ HC.search (ops t) (eff c) bs es n fl fc x i q

/// Entry `i` stores `x`'s hash code and a key `c` deems equal to `x`.
let hit (#t: Type0) (es: seq (entry t)) (c: option (Eq.comparer t)) (x: t) (i: int) : prop =
  HC.hit (ops t) (eff c) es (HC.hv (eff c) x) x i

let search_start (#t: Type0) (bs: seq I32.t) (es: seq (entry t)) (n fl fc: int) (c: option (Eq.comparer t)) (x: t)
  : Lemma (requires wf bs es n fl fc c /\ Seq.length es > 0)
          (ensures search bs es n fl fc c x (bucket bs es c x - 1) 0 /\
                   0 <= bucket bs es c x /\ bucket bs es c x <= Seq.length es)
  = HC.search_start (ops t) (eff c) bs es n fl fc x

let search_step (#t: Type0) (bs: seq I32.t) (es: seq (entry t)) (n fl fc: int) (c: option (Eq.comparer t))
                (x: t) (i q: int)
  : Lemma (requires search bs es n fl fc c x i q /\ 0 <= i /\ i < Seq.length es /\ ~ (hit es c x i))
          (ensures search bs es n fl fc c x (I32.v (Seq.index es i).E.fld_Next) (q + 1) /\
                   q + 1 <= Seq.length es)
  = HC.search_step (ops t) (eff c) bs es n fl fc x i q

let search_hit (#t: Type0) (bs: seq I32.t) (es: seq (entry t)) (n fl fc: int) (c: option (Eq.comparer t))
               (x: t) (i q: int)
  : Lemma (requires search bs es n fl fc c x i q /\ hit es c x i)
          (ensures mem c (items es n) x)
  = HC.search_hit (ops t) (eff c) bs es n fl fc x i q

let search_absent (#t: Type0) (bs: seq I32.t) (es: seq (entry t)) (n fl fc: int) (c: option (Eq.comparer t))
                  (x: t) (i q: int)
  : Lemma (requires search bs es n fl fc c x i q /\ ~ (0 <= i /\ i < Seq.length es))
          (ensures ~ (mem c (items es n) x))
  = HC.search_absent (ops t) (eff c) bs es n fl fc x i q

(* ---------------------------------------------------------------------------------- *)
(* Remove *)

/// `search`, with `last` the entry before `i` in the chain (-1 at its head).
let search_last (#t: Type0) (bs: seq I32.t) (es: seq (entry t)) (n fl fc: int) (c: option (Eq.comparer t))
                (x: t) (i q last: int) : prop =
  q >= 0 /\ HC.search_last (ops t) (eff c) bs es n fl fc x i q last

let search_last_start (#t: Type0) (bs: seq I32.t) (es: seq (entry t)) (n fl fc: int) (c: option (Eq.comparer t)) (x: t)
  : Lemma (requires wf bs es n fl fc c /\ Seq.length es > 0)
          (ensures search_last bs es n fl fc c x (bucket bs es c x - 1) 0 (-1))
  = HC.search_last_start (ops t) (eff c) bs es n fl fc x

let search_last_step (#t: Type0) (bs: seq I32.t) (es: seq (entry t)) (n fl fc: int) (c: option (Eq.comparer t))
                     (x: t) (i q last: int)
  : Lemma (requires search_last bs es n fl fc c x i q last /\ 0 <= i /\ i < Seq.length es /\ ~ (hit es c x i))
          (ensures search_last bs es n fl fc c x (I32.v (Seq.index es i).E.fld_Next) (q + 1) i /\
                   q + 1 <= Seq.length es)
  = HC.search_last_step (ops t) (eff c) bs es n fl fc x i q last

let search_next (#t: Type0) (bs: seq I32.t) (es: seq (entry t)) (n fl fc: int) (c: option (Eq.comparer t))
                (x: t) (i q last: int)
  : Lemma (requires search_last bs es n fl fc c x i q last /\ 0 <= i /\ i < Seq.length es)
          (ensures -1 <= I32.v (Seq.index es i).E.fld_Next /\ I32.v (Seq.index es i).E.fld_Next < Seq.length es /\
                   -1 <= fl /\ fl < Seq.length es /\
                   (last < 0 \/ (0 <= last /\ last < Seq.length es /\ last <> i)))
  = HC.search_next (ops t) (eff c) bs es n fl fc x i q;
    let b = HC.bkt (HC.hv (eff c) x) (Seq.length es) in
    let h = I32.v (Seq.index bs b) - 1 in
    let l = HC.chain_of (ops t) (eff c) bs es n fl fc b in
    if q >= l then HC.walk_end (ops t) es h l q;
    if q > 0 then begin
      HC.chain_live (ops t) es n (-1) b h l (q - 1);
      HC.chain_distinct (ops t) es n (-1) b h l (q - 1) q
    end

let search_last_absent (#t: Type0) (bs: seq I32.t) (es: seq (entry t)) (n fl fc: int) (c: option (Eq.comparer t))
                       (x: t) (i q last: int)
  : Lemma (requires search_last bs es n fl fc c x i q last /\ ~ (0 <= i /\ i < Seq.length es))
          (ensures ~ (mem c (items es n) x))
  = HC.search_absent (ops t) (eff c) bs es n fl fc x i q

/// `ys` is `xs` without one element equal to `x` at the comparer `c`.
let removed (#t: Type0) (c: option (Eq.comparer t)) (xs ys: seq t) (x: t) : prop =
  exists (p: nat). p < Seq.length xs /\ Eq.equals (eff c) (Seq.index xs p) x /\ ys == HC.remove_at xs p

/// What `Remove` writes on finding `x` at entry `i`, behind `last` (HC.remove_writes).
let remove_writes (#t: Type0) (bs bs': seq I32.t) (es es': seq (entry t)) (c: option (Eq.comparer t))
                  (x: t) (fl i last: int) : prop =
  Seq.length es > 0 /\
  HC.remove_writes (ops t) bs bs' es es' (HC.bkt (HC.hv (eff c) x) (Seq.length es)) fl i last

let remove_ok (#t: Type0) (bs bs': seq I32.t) (es es': seq (entry t)) (n fl fc: int) (c: option (Eq.comparer t))
              (x: t) (i q last: int)
  : Lemma (requires search_last bs es n fl fc c x i q last /\ hit es c x i /\
                    remove_writes bs bs' es es' c x fl i last)
          (ensures wf bs' es' n i (fc + 1) c /\ fc + 1 <= n /\
                   mem c (items es n) x /\ removed c (items es n) (items es' n) x)
  = HC.remove_ok (ops t) (eff c) bs bs' es es' n fl fc x i q last;
    HC.wf_count (ops t) (eff c) bs' es' n i (fc + 1)

(* ---------------------------------------------------------------------------------- *)
(* Enumerator *)

/// `prefixes es n` at `i` is the live elements among the first `i` entries, `i <= n`.
let prefixes (#t: Type0) (es: seq (entry t)) (n: int) : seq (seq t) =
  if 0 <= n && n <= Seq.length es
  then Seq.init (n + 1) (fun (i: nat{i < n + 1}) -> items es i)
  else Seq.empty

/// One step of the walk: entry `i` adds its value when it is live.
let items_step (#t: Type0) (es: seq (entry t)) (i: int)
  : Lemma (requires 0 <= i /\ i < Seq.length es)
          (ensures items es (i + 1) ==
                   (if I32.v (Seq.index es i).E.fld_Next >= -1
                    then Seq.snoc (items es i) (Seq.index es i).E.fld_Value
                    else items es i))
  = ()

/// The live values among the first `i` entries are a prefix of those among the first `n`.
let rec items_prefix (#t: Type0) (es: seq (entry t)) (i n: int)
  : Lemma (requires 0 <= i /\ i <= n /\ n <= Seq.length es)
          (ensures Seq.length (items es i) <= Seq.length (items es n) /\
                   items es i == Seq.slice (items es n) 0 (Seq.length (items es i)))
          (decreases n - i)
  = if i = n then Seq.lemma_eq_intro (items es i) (Seq.slice (items es n) 0 (Seq.length (items es i)))
    else begin
      items_prefix es i (n - 1);
      items_step es (n - 1);
      let a = items es (n - 1) in
      let b = items es n in
      let k = Seq.length (items es i) in
      Seq.lemma_eq_intro (Seq.slice a 0 k) (Seq.slice b 0 k)
    end

/// The live values number the entries in use less the free ones.
let items_count (#t: Type0) (bs: seq I32.t) (es: seq (entry t)) (n fl fc: int) (c: option (Eq.comparer t))
  : Lemma (requires 0 <= fc /\ fc <= n /\ (n == 0 \/ wf bs es n fl fc c))
          (ensures Seq.length (items es n) == n - fc)
  = if n = 0 then () else HC.count_items (ops t) es n (-1)

(* ---------------------------------------------------------------------------------- *)
(* Sizes, fresh tables *)

module HI = Pulse.Lib.CSharp.HashInsert
module HS = Pulse.Lib.CSharp.HashSize

/// A table size `HashHelpers` hands out: at least 3 and prime.
let prime_size (n: int) : prop = HS.prime_size n

/// Every bucket is 0: a new `int[]`.
let zeros (bs: seq I32.t) : prop =
  forall (b: nat). {:pattern Seq.index bs b} b < Seq.length bs ==> I32.v (Seq.index bs b) == 0

/// A table with no entries in use is well formed, over any entries.
let wf_fresh (#t: Type0) (bs: seq I32.t) (es: seq (entry t)) (c: option (Eq.comparer t))
  : Lemma (requires Seq.length bs == Seq.length es /\ zeros bs)
          (ensures wf bs es 0 (-1) 0 c /\ items es 0 == Seq.empty)
  = HC.wf_empty (ops t) (eff c) bs es

(* ---------------------------------------------------------------------------------- *)
(* AddIfNotPresent *)

/// `ys` is `xs` with `x` inserted at some position.
let added (#t: Type0) (xs ys: seq t) (x: t) : prop =
  exists (p: nat). p <= Seq.length xs /\ ys == HC.insert_at xs p x

/// The free list's successor of entry `i`: `StartOfFreeList - entries[i].Next`.
let fnext (#t: Type0) (es: seq (entry t)) (i: int) : int = HC.fnxt (ops t) es i

let insert_pre (#t: Type0) (bs: seq I32.t) (es: seq (entry t)) (n fl fc: int) (c: option (Eq.comparer t)) (x: t)
  : Lemma (requires wf bs es n fl fc c /\ Seq.length es > 0)
          (ensures 0 <= bucket bs es c x /\ bucket bs es c x <= Seq.length es /\
                   (fc > 0 ==> 0 <= fl /\ fl < n /\ -1 <= fnext es fl /\ fnext es fl < n) /\
                   (fc == 0 ==> fl == -1) /\ fc <= n)
  = HI.insert_pre (ops t) (eff c) bs es n fl fc x

/// What the code writes: entry `i` holds `x`, its hash at `c` and the bucket's old head,
/// and the bucket now points at it.
let insert_writes (#t: Type0) (bs bs': seq I32.t) (es es': seq (entry t)) (c: option (Eq.comparer t)) (x: t) (i: int) : prop =
  HI.insert_writes (ops t) (eff c) bs bs' es es' x i

/// The insertion, from the free list (the fields after it: `n` entries in use, `fl'`,
/// `fc'`; `i` was the head) or at the end (`i == n0`).
let insert_ok (#t: Type0) (bs bs': seq I32.t) (es es': seq (entry t)) (n0 n1 fl1 fc1 i: int)
              (c: option (Eq.comparer t)) (x: t)
  : Lemma (requires insert_writes bs bs' es es' c x i /\
                    ((n1 == n0 /\ fc1 >= 0 /\ wf bs es n0 i (fc1 + 1) c /\ fl1 == fnext es i) \/
                     (fc1 == 0 /\ i == n0 /\ n1 == n0 + 1 /\ wf bs es n0 fl1 0 c)))
          (ensures wf bs' es' n1 fl1 fc1 c /\ added (items es n0) (items es' n1) x /\
                   Seq.length (items es' n1) == Seq.length (items es n0) + 1)
  = let o = ops t in
    if n1 <> n0 + 1
    then HI.insert_ok o o.key (eff c) bs bs' es es' n0 i (fc1 + 1) x i n1 fl1 fc1
    else HI.insert_ok o o.key (eff c) bs bs' es es' n0 fl1 0 x i n1 fl1 fc1

(* ---------------------------------------------------------------------------------- *)
(* Resize *)

/// `entries` agrees with `old` below `n`: `Array.Copy(old, entries, n)`.
let same_prefix (#t: Type0) (old es: seq (entry t)) (n: int) : prop =
  0 <= n /\ n <= Seq.length old /\ n <= Seq.length es /\
  (forall (j: nat). {:pattern Seq.index es j} j < n ==> Seq.index es j == Seq.index old j)

/// The table without its chains: the entries in use, the free list and the hash codes.
let pre_wf (#t: Type0) (es: seq (entry t)) (n fl fc: int) (c: option (Eq.comparer t)) : prop =
  HI.pre_wf (ops t) (eff c) es n fl fc

let copy_ok (#t: Type0) (bs: seq I32.t) (old es: seq (entry t)) (n fl fc: int) (c: option (Eq.comparer t))
  : Lemma (requires wf bs old n fl fc c /\ same_prefix old es n)
          (ensures pre_wf es n fl fc c /\ items es n == items old n)
  = let o = ops t in HI.copy_ok o o.key (eff c) bs old es n fl fc

/// The rebuild has linked the entries below `i` into `bs`, the rest are `src`'s.
let rebuilt (#t: Type0) (bs: seq I32.t) (src es: seq (entry t)) (n i: int) : prop =
  HI.rebuilt (ops t) bs src es n i

let rebuild_start (#t: Type0) (bs: seq I32.t) (src: seq (entry t)) (n: int)
  : Lemma (requires 0 <= n /\ n <= Seq.length src /\ Seq.length src > 0 /\ Seq.length bs == Seq.length src /\ zeros bs)
          (ensures rebuilt bs src src n 0)
  = HI.rebuild_start (ops t) bs src n

/// The bucket of entry `i`, as stored (1-based).
let slot (#t: Type0) (bs: seq I32.t) (es: seq (entry t)) (i: int) : int =
  if 0 <= i && i < Seq.length es && Seq.length bs = Seq.length es
  then I32.v (Seq.index bs (HC.bkt (I32.v (Seq.index es i).E.fld_HashCode) (Seq.length es)))
  else 0

let rebuild_bucket (#t: Type0) (bs: seq I32.t) (src es: seq (entry t)) (n i: int)
  : Lemma (requires rebuilt bs src es n i /\ i < n)
          (ensures 0 <= slot bs es i /\ slot bs es i <= Seq.length es)
  = HI.rebuild_bucket (ops t) bs src es n i

/// `entry.Next = bucket - 1; bucket = i + 1` for a live entry `i`; nothing for a dead one.
let link_writes (#t: Type0) (bs bs': seq I32.t) (es es': seq (entry t)) (i: int) : prop =
  HI.link_writes (ops t) bs bs' es es' i

let rebuild_step (#t: Type0) (bs bs': seq I32.t) (src es es': seq (entry t)) (n i: int)
  : Lemma (requires rebuilt bs src es n i /\ i < n /\ link_writes bs bs' es es' i)
          (ensures rebuilt bs' src es' n (i + 1))
  = HI.rebuild_step (ops t) bs bs' src es es' n i

let rebuild_done (#t: Type0) (bs: seq I32.t) (src es: seq (entry t)) (n fl fc: int) (c: option (Eq.comparer t))
  : Lemma (requires pre_wf src n fl fc c /\ rebuilt bs src es n n)
          (ensures wf bs es n fl fc c /\ items es n == items src n)
  = let o = ops t in HI.rebuild_done o o.key (eff c) bs src es n fl fc

(* ---------------------------------------------------------------------------------- *)
(* The collision path: a string set switches to the randomized comparer and rehashes   *)

module SC = Pulse.Lib.CSharp.StringComparers

/// `_comparer is NonRandomizedStringEqualityComparer`.
let non_randomized (#t: Type0) (c: option (Eq.comparer t)) : bool =
  Some? c && SC.is_non_randomized (Some?.v c)

/// `c.GetRandomizedEqualityComparer()`, as the field holds it.
let randomized (#t: Type0) (c: option (Eq.comparer t)) : option (Eq.comparer t) =
  match c with
  | Some h -> Some (SC.randomized h)
  | None -> None

/// Two comparers deem the same elements equal.
let same_equality (#t: Type0) (c0 c1: option (Eq.comparer t)) : prop =
  forall (x y: t). Eq.equals (eff c0) x y == Eq.equals (eff c1) x y

let same_refl (#t: Type0) (c: option (Eq.comparer t)) : Lemma (same_equality c c) = ()

let randomized_same (#t: Type0) (c: option (Eq.comparer t))
  : Lemma (requires non_randomized c)
          (ensures same_equality c (randomized c) /\ Some? (randomized c))
  = ()

let mem_same (#t: Type0) (c0 c1: option (Eq.comparer t)) (xs: seq t) (x: t)
  : Lemma (requires same_equality c0 c1) (ensures mem c0 xs x <==> mem c1 xs x)
  = ()

/// What is added is a member, under a comparer for which it equals itself.
let added_mem (#t: Type0) (c: option (Eq.comparer t)) (xs ys: seq t) (x: t)
  : Lemma (requires added xs ys x /\ Eq.equals (eff c) x x) (ensures mem c ys x)
  = let p = FStar.IndefiniteDescription.indefinite_description_ghost nat
              (fun p -> p <= Seq.length xs /\ ys == HC.insert_at xs p x) in
    assert (Seq.index ys p == x)

/// A non-randomized comparer's equality is reflexive.
let non_randomized_refl (#t: Type0) (c: option (Eq.comparer t)) (x: t)
  : Lemma (requires non_randomized c) (ensures Eq.equals (eff c) x x)
  = SC.non_randomized_refl #t (Some?.v c) x

/// The entries below `i` are rehashed with `c`; the rest are `src`'s.
let rehashed (#t: Type0) (src es: seq (entry t)) (n i: int) (c: option (Eq.comparer t)) : prop =
  HI.rehashed (ops t) (eff c) src es n i

let rehash_start (#t: Type0) (src: seq (entry t)) (n: int) (c: option (Eq.comparer t))
  : Lemma (requires 0 <= n /\ n <= Seq.length src) (ensures rehashed src src n 0 c)
  = HI.rehash_start (ops t) (eff c) src n

/// `entry.HashCode = …` at a live entry `i`; nothing at a dead one.
let rehash_writes (#t: Type0) (es es': seq (entry t)) (i: int) (c: option (Eq.comparer t)) : prop =
  0 <= i /\ i < Seq.length es /\ Seq.length es' == Seq.length es /\
  (forall (j: nat). j < Seq.length es /\ j <> i ==> Seq.index es' j == Seq.index es j) /\
  (let o = ops t in
   if o.HC.nx (Seq.index es i) >= -1
   then o.HC.nx (Seq.index es' i) == o.HC.nx (Seq.index es i) /\
        o.HC.key (Seq.index es' i) == o.HC.key (Seq.index es i) /\
        o.HC.hc (Seq.index es' i) == HC.hv (eff c) (o.HC.key (Seq.index es i))
   else Seq.index es' i == Seq.index es i)

let rehash_step (#t: Type0) (src es es': seq (entry t)) (n i: int) (c: option (Eq.comparer t))
  : Lemma (requires rehashed src es n i c /\ i < n /\ rehash_writes es es' i c)
          (ensures rehashed src es' n (i + 1) c)
  = HI.rehash_step (ops t) (eff c) src es es' n i

/// The free list of a table, without its chains or its hash codes.
let pre_free (#t: Type0) (es: seq (entry t)) (n fl fc: int) : prop =
  0 <= n /\ n <= Seq.length es /\ HC.free_ok (ops t) es n (-1) fl fc

let pre_free_of (#t: Type0) (es: seq (entry t)) (n fl fc: int) (c: option (Eq.comparer t))
  : Lemma (requires pre_wf es n fl fc c) (ensures pre_free es n fl fc)
  = ()

let rehash_done (#t: Type0) (src es: seq (entry t)) (n fl fc: int) (c: option (Eq.comparer t))
  : Lemma (requires pre_free src n fl fc /\ rehashed src es n n c)
          (ensures pre_wf es n fl fc c /\ items es n == items src n)
  = let o = ops t in
    assert (forall (j: int). HC.dead o src n (-1) j == HC.dead o es n (-1) j);
    HC.items_frame o src es n (-1);
    HC.free_same o src es n (-1) (-1) fl fc

(* ---------------------------------------------------------------------------------- *)
(* The constructor's swap to a non-randomized string comparer (R30.18)                 *)

module SCO = Pulse.Lib.CSharp.StringComparerOf
module Obj = Pulse.Lib.CSharp.Obj

/// `_comparer = (IEqualityComparer<T>)stringComparer` keeps the set's equality, when
/// `stringComparer` is what `GetStringComparer(_comparer)` gave back for a string set.
let string_swap_ok (#t: Type0) (c: option (Eq.comparer t)) : prop =
  (Eq.type_of t == Eq.type_of string /\ Some? c /\ Some? (SCO.string_comparer (Obj.box #(option (Eq.comparer t)) c)))
  ==> same_equality c (Some (Some?.v (SCO.string_comparer (Obj.box #(option (Eq.comparer t)) c))))

let string_swap (#t: Type0) (c: option (Eq.comparer t)) : Lemma (string_swap_ok c) =
  match c, SCO.string_comparer (Obj.box #(option (Eq.comparer t)) c) with
  | Some c', Some h ->
    let step (x y: t)
      : Lemma (Eq.type_of t == Eq.type_of string ==> Eq.equals (eff c) x y == Eq.equals (eff #t (Some h)) x y) =
      Classical.move_requires (SCO.string_comparer_equals #t c' h x) y in
    Classical.forall_intro_2 step
  | _ -> ()

(* ---------------------------------------------------------------------------------- *)
(* Compacting into new arrays (`CopyEntries`, for `TrimExcess`)                        *)

let compactable (#t: Type0) (old: seq (entry t)) (n: int) (c: option (Eq.comparer t)) : prop =
  0 <= n /\ n <= Seq.length old /\ HC.hashes_ok (ops t) (eff c) old n (-1)

let wf_compactable (#t: Type0) (bs: seq I32.t) (old: seq (entry t)) (n fl fc: int) (c: option (Eq.comparer t))
  : Lemma (requires wf bs old n fl fc c /\ 0 <= fc /\ fc <= n)
          (ensures compactable old n c /\ Seq.length (items old n) == n - fc)
  = items_count bs old n fl fc c

let compacted (#t: Type0) (bs: seq I32.t) (old es: seq (entry t)) (n i m: int) (c: option (Eq.comparer t)) : prop =
  let o = ops t in
  HI.compacted o o.key (eff c) bs old es n i m /\ Seq.length (items old n) <= Seq.length es

let compact_start (#t: Type0) (bs: seq I32.t) (old es: seq (entry t)) (n: int) (c: option (Eq.comparer t))
  : Lemma (requires compactable old n c /\ Seq.length es > 0 /\ Seq.length bs == Seq.length es /\ zeros bs /\
                    Seq.length (items old n) <= Seq.length es)
          (ensures compacted bs old es n 0 0 c)
  = let o = ops t in HI.compact_start o o.key (eff c) bs old es n

/// The slot `old[i]` goes to in `es`'s buckets.
let old_slot (#t: Type0) (bs: seq I32.t) (old es: seq (entry t)) (i: int) : int =
  if 0 <= i && i < Seq.length old && Seq.length bs = Seq.length es && Seq.length es > 0
  then I32.v (Seq.index bs (HC.bkt (I32.v (Seq.index old i).E.fld_HashCode) (Seq.length es)))
  else 0

let compact_room (#t: Type0) (bs: seq I32.t) (old es: seq (entry t)) (n i m: int) (c: option (Eq.comparer t))
  : Lemma (requires compacted bs old es n i m c /\ i < n /\ I32.v (Seq.index old i).E.fld_Next >= -1)
          (ensures m < Seq.length es /\ 0 <= m /\ 0 <= old_slot bs old es i /\ old_slot bs old es i <= Seq.length es)
  = let o = ops t in HI.compact_room o o.key (eff c) bs old es n i m

/// What the step at `old[i]` wrote: when it is live, it is copied to `es[m]`, linked at
/// the head of its bucket, and `m` grew by one; otherwise nothing.
let compact_writes (#t: Type0) (bs bs': seq I32.t) (old es es': seq (entry t)) (i m m': int) : prop =
  0 <= i /\ i < Seq.length old /\
  (if I32.v (Seq.index old i).E.fld_Next >= -1
   then HI.copy_writes (ops t) bs bs' old es es' i m /\ m' == m + 1
   else es' == es /\ bs' == bs /\ m' == m)

let compact_step (#t: Type0) (bs bs': seq I32.t) (old es es': seq (entry t)) (n i m m': int) (c: option (Eq.comparer t))
  : Lemma (requires compacted bs old es n i m c /\ i < n /\ compact_writes bs bs' old es es' i m m')
          (ensures compacted bs' old es' n (i + 1) m' c)
  = let o = ops t in HI.compact_step o o.key (eff c) bs bs' old es es' n i m

let compact_done (#t: Type0) (bs: seq I32.t) (old es: seq (entry t)) (n m: int) (c: option (Eq.comparer t))
  : Lemma (requires compacted bs old es n n m c)
          (ensures wf bs es m (-1) 0 c /\ items es m == items old n /\ m <= Seq.length es /\
                   Seq.length (items es m) == m)
  = let o = ops t in
    HI.compact_done o o.key (eff c) bs old es n m;
    items_count bs es m (-1) 0 c

(* ---------------------------------------------------------------------------------- *)
(* IsSubsetOf *)

/// Every element of `xs` is a member of `s` at the comparer `c`.
let all_in (#t: Type0) (c: option (Eq.comparer t)) (s xs: seq t) : prop =
  forall (i: nat). i < Seq.length xs ==> mem c s (Seq.index xs i)

/// Appending `x` adds exactly `x`'s membership.
let all_in_snoc (#t: Type0) (c: option (Eq.comparer t)) (s xs: seq t) (x: t)
  : Lemma (all_in c s (Seq.snoc xs x) <==> (all_in c s xs /\ mem c s x))
          [SMTPat (all_in c s (Seq.snoc xs x))]
  = let ys = Seq.snoc xs x in
    assert (forall (i: nat). i < Seq.length xs ==> Seq.index ys i == Seq.index xs i);
    assert (Seq.index ys (Seq.length xs) == x)

/// `ps` are the prefixes of a walk ending at `xs`.
let walk (#t: Type0) (ps: seq (seq t)) (xs: seq t) : prop =
  Seq.length ps >= 1 /\ Seq.index ps (Seq.length ps - 1) == xs /\
  (forall (i: nat). i < Seq.length ps ==>
     Seq.length (Seq.index ps i) <= Seq.length xs /\
     Seq.index ps i == Seq.slice xs 0 (Seq.length (Seq.index ps i)))

/// The walk over the first `n` entries: nothing before entry 0, every live element at `n`.
let prefixes_walk (#t: Type0) (es: seq (entry t)) (n: int)
  : Lemma (requires 0 <= n /\ n <= Seq.length es)
          (ensures Seq.length (prefixes es n) == n + 1 /\
                   Seq.length (Seq.index (prefixes es n) 0) == 0 /\
                   walk (prefixes es n) (items es n))
  = let ps = prefixes es n in
    let aux (i: nat)
      : Lemma (i < Seq.length ps ==>
                 Seq.length (Seq.index ps i) <= Seq.length (items es n) /\
                 Seq.index ps i == Seq.slice (items es n) 0 (Seq.length (Seq.index ps i)))
      = if i < Seq.length ps then items_prefix es i n in
    Classical.forall_intro aux

/// What fails through a prefix of the walk fails through the whole of it.
let all_in_walk (#t: Type0) (c: option (Eq.comparer t)) (s: seq t) (ps: seq (seq t)) (xs: seq t) (i: int)
  : Lemma (requires walk ps xs /\ 0 <= i /\ i < Seq.length ps /\ ~(all_in c s (Seq.index ps i)))
          (ensures ~(all_in c s xs))
  = let a = Seq.index ps i in
    assert (forall (j: nat). j < Seq.length a ==> Seq.index a j == Seq.index xs j)
