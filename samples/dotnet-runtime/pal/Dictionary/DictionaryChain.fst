module DictionaryChain

/// The glue between `Dictionary<TKey,TValue>`'s representation, as pal-csharp translates
/// it, and the separate-chaining theory in `Pulse.Lib.CSharp.HashChain` and
/// `Pulse.Lib.CSharp.HashInsert` (doc/translation.md §30). The table is keyed by the
/// entry's key; the values are the same table seen through the entry's value
/// (`HI.view`). Every definition here is a definition; nothing is assumed.

open FStar.Seq
module Seq = FStar.Seq
module I32 = FStar.Int32
module U32 = FStar.UInt32
module Cast = FStar.Int.Cast
module HC = Pulse.Lib.CSharp.HashChain
module HI = Pulse.Lib.CSharp.HashInsert
module Eq = Pulse.Lib.CSharp.Equality
module E = Struct_Dictionary_Entry

let entry (tk tv: Type0) = E.struct_Dictionary_Entry tk tv

/// The stored hash code, `(uint)comparer.GetHashCode(key)`, read back as the `int` it was.
let hc (#tk #tv: Type0) (x: entry tk tv) : int = I32.v (Cast.uint32_to_int32 x.E.fld_hashCode)

/// `Entry.hashCode`, `Entry.next` and `Entry.key`.
let ops (tk tv: Type0) : HC.ops (entry tk tv) tk = {
  HC.hc = hc #tk #tv;
  HC.nx = (fun (x: entry tk tv) -> I32.v x.E.fld_next);
  HC.key = (fun (x: entry tk tv) -> x.E.fld_key);
}

let value_of (#tk #tv: Type0) (x: entry tk tv) : tv = x.E.fld_value

/// The same table, seen through the values.
let vops (tk tv: Type0) : HC.ops (entry tk tv) tv = HI.view (ops tk tv) (value_of #tk #tv)

/// The comparer the dictionary uses: `_comparer`, or `EqualityComparer<TKey>.Default`
/// when it is null, which the constructors allow only for a value type.
let eff (#tk: Type0) (c: option (Eq.comparer tk)) : Eq.handle =
  match c with
  | None -> Eq.default_comparer tk
  | Some h -> h


let keys (#tk #tv: Type0) (es: seq (entry tk tv)) (n: int) : seq tk =
  if 0 <= n && n <= Seq.length es then HC.items (ops tk tv) es n (-1) else Seq.empty

let values (#tk #tv: Type0) (es: seq (entry tk tv)) (n: int) : seq tv =
  if 0 <= n && n <= Seq.length es then HC.items (vops tk tv) es n (-1) else Seq.empty

/// No key is null: `Add` and the indexer reject a null key.
let non_null (#tk: Type0) (ks: seq tk) : prop =
  forall (j: nat). {:pattern Seq.index ks j} j < Seq.length ks ==> ~(Eq.is_null (Seq.index ks j))

let live_non_null (#tk #tv: Type0) (es: seq (entry tk tv)) (n: int) (i: nat)
  : Lemma (requires non_null (keys es n) /\ i < n /\ n <= Seq.length es /\ I32.v (Seq.index es i).E.fld_next >= -1)
          (ensures ~(Eq.is_null (Seq.index es i).E.fld_key))
  = HC.items_index (ops tk tv) es n i

let insert_at_index (#a: Type) (s: seq a) (p: nat{p <= Seq.length s}) (x: a) (j: nat{j <= Seq.length s})
  : Lemma (Seq.index (HC.insert_at s p x) j == (if j < p then Seq.index s j else if j = p then x else Seq.index s (j - 1)))
  = let l = Seq.slice s 0 p in
    let r = Seq.cons x (Seq.slice s p (Seq.length s)) in
    if j < p then Seq.lemma_index_app1 l r j else Seq.lemma_index_app2 l r j

let remove_at_index (#a: Type) (s: seq a) (p: nat{p < Seq.length s}) (j: nat{j < Seq.length s - 1})
  : Lemma (Seq.index (HC.remove_at s p) j == (if j < p then Seq.index s j else Seq.index s (j + 1)))
  = let l = Seq.slice s 0 p in
    let r = Seq.slice s (p + 1) (Seq.length s) in
    if j < p then Seq.lemma_index_app1 l r j else Seq.lemma_index_app2 l r j

let insert_at_non_null (#tk: Type0) (ks: seq tk) (p: nat{p <= Seq.length ks}) (k: tk)
  : Lemma (requires non_null ks /\ ~(Eq.is_null k)) (ensures non_null (HC.insert_at ks p k))
  = introduce forall (j: nat). j < Seq.length (HC.insert_at ks p k) ==> ~(Eq.is_null (Seq.index (HC.insert_at ks p k) j))
    with introduce _ ==> _ with insert_at_index ks p k j

let remove_at_non_null (#tk: Type0) (ks: seq tk) (p: nat{p < Seq.length ks})
  : Lemma (requires non_null ks) (ensures non_null (HC.remove_at ks p))
  = introduce forall (j: nat). j < Seq.length (HC.remove_at ks p) ==> ~(Eq.is_null (Seq.index (HC.remove_at ks p) j))
    with introduce _ ==> _ with remove_at_index ks p j

/// The chain invariant, plus: no live key is null.
let wf (#tk #tv: Type0) (bs: seq I32.t) (es: seq (entry tk tv)) (n fl fc: int) (c: option (Eq.comparer tk)) : prop =
  HC.wf (ops tk tv) (eff c) bs es n fl fc /\ non_null (keys es n)

let lengths (#tk #tv: Type0) (es: seq (entry tk tv)) (n: int)
  : Lemma (Seq.length (values es n) == Seq.length (keys es n))
          [SMTPat (values es n)]
  = if 0 <= n && n <= Seq.length es then HI.items_len_view (ops tk tv) (value_of #tk #tv) es n (-1)

let mem (#tk: Type0) (c: option (Eq.comparer tk)) (xs: seq tk) (x: tk) : prop =
  HC.mem (eff c) xs x

/// The cast the code stores the hash code through is undone by the one `hc` reads it with.
let cast_round (h: I32.t)
  : Lemma (Cast.uint32_to_int32 (Cast.int32_to_uint32 h) == h)
          [SMTPat (Cast.uint32_to_int32 (Cast.int32_to_uint32 h))]
  = FStar.Math.Lemmas.small_mod (I32.v h % 4294967296) 4294967296;
    assert (I32.v (Cast.uint32_to_int32 (Cast.int32_to_uint32 h)) == I32.v h)

/// Two stored hash codes are equal exactly when the `int`s they were cast from are.
let cast_inj (a: U32.t) (h: I32.t)
  : Lemma ((a == Cast.int32_to_uint32 h) <==> (Cast.uint32_to_int32 a == h))
  = let b = Cast.uint32_to_int32 a in
    assert (Cast.int32_to_uint32 b == a)

/// `∃ p. c.Equals(ks[p], k) ∧ vs[p] == v`: the dictionary maps `k` to `v`.
let maps (#tk #tv: Type0) (c: option (Eq.comparer tk)) (ks: seq tk) (vs: seq tv) (k: tk) (v: tv) : prop =
  exists (p: nat). p < Seq.length ks /\ p < Seq.length vs /\ Eq.equals (eff c) (Seq.index ks p) k /\ Seq.index vs p == v

(* ---------------------------------------------------------------------------------- *)
(* Searching a chain (FindValue, TryInsert, Remove) *)

/// The bucket `k` hashes to, at the comparer `c`, as stored (1-based).
let bucket (#tk #tv: Type0) (bs: seq I32.t) (es: seq (entry tk tv)) (c: option (Eq.comparer tk)) (k: tk) : int =
  if Seq.length es > 0 && Seq.length bs = Seq.length es
  then I32.v (Seq.index bs (HC.bkt (HC.hv (eff c) k) (Seq.length es)))
  else 0

let search (#tk #tv: Type0) (bs: seq I32.t) (es: seq (entry tk tv)) (n fl fc: int) (c: option (Eq.comparer tk))
           (k: tk) (i q: int) : prop =
  q >= 0 /\ HC.search (ops tk tv) (eff c) bs es n fl fc k i q /\ non_null (keys es n)

/// Entry `i` stores `(uint)` of `k`'s hash code and a key `c` deems equal to `k`: the
/// code's test.
let hit (#tk #tv: Type0) (es: seq (entry tk tv)) (c: option (Eq.comparer tk)) (k: tk) (i: int) : prop =
  0 <= i /\ i < Seq.length es /\
  (Seq.index es i).E.fld_hashCode == Cast.int32_to_uint32 (Eq.hash (eff c) k) /\
  Eq.equals (eff c) (Seq.index es i).E.fld_key k

let hit_iff (#tk #tv: Type0) (es: seq (entry tk tv)) (c: option (Eq.comparer tk)) (k: tk) (i: int)
  : Lemma (hit es c k i <==> HC.hit (ops tk tv) (eff c) es (HC.hv (eff c) k) k i)
  = if 0 <= i && i < Seq.length es then cast_inj (Seq.index es i).E.fld_hashCode (Eq.hash (eff c) k)

let search_start (#tk #tv: Type0) (bs: seq I32.t) (es: seq (entry tk tv)) (n fl fc: int) (c: option (Eq.comparer tk)) (k: tk)
  : Lemma (requires wf bs es n fl fc c /\ Seq.length es > 0)
          (ensures search bs es n fl fc c k (bucket bs es c k - 1) 0 /\
                   0 <= bucket bs es c k /\ bucket bs es c k <= Seq.length es)
  = HC.search_start (ops tk tv) (eff c) bs es n fl fc k

let search_step (#tk #tv: Type0) (bs: seq I32.t) (es: seq (entry tk tv)) (n fl fc: int) (c: option (Eq.comparer tk))
                (k: tk) (i q: int)
  : Lemma (requires search bs es n fl fc c k i q /\ 0 <= i /\ i < Seq.length es /\ ~ (hit es c k i))
          (ensures search bs es n fl fc c k (I32.v (Seq.index es i).E.fld_next) (q + 1) /\
                   q + 1 <= Seq.length es)
  = hit_iff es c k i;
    HC.search_step (ops tk tv) (eff c) bs es n fl fc k i q

/// A hit: `k` is a key, and the dictionary maps it to entry `i`'s value, which sits at the
/// same position among the values as its key among the keys.
let search_hit (#tk #tv: Type0) (bs: seq I32.t) (es: seq (entry tk tv)) (n fl fc: int) (c: option (Eq.comparer tk))
               (k: tk) (i q: int)
  : Lemma (requires search bs es n fl fc c k i q /\ hit es c k i)
          (ensures mem c (keys es n) k /\ maps c (keys es n) (values es n) k (Seq.index es i).E.fld_value /\
                   0 <= i /\ i < n)
  = let o = ops tk tv in
    hit_iff es c k i;
    HC.search_hit o (eff c) bs es n fl fc k i q;
    HC.items_index o es n i;
    HC.items_index (vops tk tv) es n i;
    HI.pos_view o (value_of #tk #tv) es i

let search_absent (#tk #tv: Type0) (bs: seq I32.t) (es: seq (entry tk tv)) (n fl fc: int) (c: option (Eq.comparer tk))
                  (k: tk) (i q: int)
  : Lemma (requires search bs es n fl fc c k i q /\ ~ (0 <= i /\ i < Seq.length es))
          (ensures ~ (mem c (keys es n) k))
  = HC.search_absent (ops tk tv) (eff c) bs es n fl fc k i q

(* ---------------------------------------------------------------------------------- *)
(* Remove *)

let search_last (#tk #tv: Type0) (bs: seq I32.t) (es: seq (entry tk tv)) (n fl fc: int) (c: option (Eq.comparer tk))
                (k: tk) (i q last: int) : prop =
  q >= 0 /\ HC.search_last (ops tk tv) (eff c) bs es n fl fc k i q last /\ non_null (keys es n)

let search_last_start (#tk #tv: Type0) (bs: seq I32.t) (es: seq (entry tk tv)) (n fl fc: int) (c: option (Eq.comparer tk)) (k: tk)
  : Lemma (requires wf bs es n fl fc c /\ Seq.length es > 0)
          (ensures search_last bs es n fl fc c k (bucket bs es c k - 1) 0 (-1) /\
                   0 <= bucket bs es c k /\ bucket bs es c k <= Seq.length es)
  = HC.search_last_start (ops tk tv) (eff c) bs es n fl fc k;
    HC.search_start (ops tk tv) (eff c) bs es n fl fc k

let search_last_step (#tk #tv: Type0) (bs: seq I32.t) (es: seq (entry tk tv)) (n fl fc: int) (c: option (Eq.comparer tk))
                     (k: tk) (i q last: int)
  : Lemma (requires search_last bs es n fl fc c k i q last /\ 0 <= i /\ i < Seq.length es /\ ~ (hit es c k i))
          (ensures search_last bs es n fl fc c k (I32.v (Seq.index es i).E.fld_next) (q + 1) i /\
                   q + 1 <= Seq.length es)
  = hit_iff es c k i;
    HC.search_last_step (ops tk tv) (eff c) bs es n fl fc k i q last

let search_next (#tk #tv: Type0) (bs: seq I32.t) (es: seq (entry tk tv)) (n fl fc: int) (c: option (Eq.comparer tk))
                (k: tk) (i q last: int)
  : Lemma (requires search_last bs es n fl fc c k i q last /\ 0 <= i /\ i < Seq.length es)
          (ensures -1 <= I32.v (Seq.index es i).E.fld_next /\ I32.v (Seq.index es i).E.fld_next < Seq.length es /\
                   -1 <= fl /\ fl < Seq.length es /\
                   (last < 0 \/ (0 <= last /\ last < Seq.length es /\ last <> i)))
  = HC.search_next (ops tk tv) (eff c) bs es n fl fc k i q;
    let b = HC.bkt (HC.hv (eff c) k) (Seq.length es) in
    let h = I32.v (Seq.index bs b) - 1 in
    let l = HC.chain_of (ops tk tv) (eff c) bs es n fl fc b in
    if q >= l then HC.walk_end (ops tk tv) es h l q;
    if q > 0 then begin
      HC.chain_live (ops tk tv) es n (-1) b h l (q - 1);
      HC.chain_distinct (ops tk tv) es n (-1) b h l (q - 1) q
    end

let search_last_absent (#tk #tv: Type0) (bs: seq I32.t) (es: seq (entry tk tv)) (n fl fc: int) (c: option (Eq.comparer tk))
                       (k: tk) (i q last: int)
  : Lemma (requires search_last bs es n fl fc c k i q last /\ ~ (0 <= i /\ i < Seq.length es))
          (ensures ~ (mem c (keys es n) k))
  = HC.search_absent (ops tk tv) (eff c) bs es n fl fc k i q

/// `ks'`/`vs'` are `ks`/`vs` without the pair at one position, whose key `c` deems equal
/// to `k` and whose value is `v`.
let removed (#tk #tv: Type0) (c: option (Eq.comparer tk)) (ks: seq tk) (vs: seq tv) (ks': seq tk) (vs': seq tv)
            (k: tk) (v: tv) : prop =
  exists (p: nat). p < Seq.length ks /\ p < Seq.length vs /\ Eq.equals (eff c) (Seq.index ks p) k /\
              Seq.index vs p == v /\ ks' == HC.remove_at ks p /\ vs' == HC.remove_at vs p

/// What `Remove` writes on finding `k` at entry `i`, behind `last`: the generic unlinking
/// (HC.remove_writes), keeping the value of `last`, which the code does not touch.
let remove_writes (#tk #tv: Type0) (bs bs': seq I32.t) (es es': seq (entry tk tv)) (c: option (Eq.comparer tk))
                  (k: tk) (fl i last: int) : prop =
  Seq.length es > 0 /\
  HC.remove_writes (ops tk tv) bs bs' es es' (HC.bkt (HC.hv (eff c) k) (Seq.length es)) fl i last /\
  (last >= 0 ==> (Seq.index es' last).E.fld_value == (Seq.index es last).E.fld_value)

#push-options "--z3rlimit 40"
let remove_ok (#tk #tv: Type0) (bs bs': seq I32.t) (es es': seq (entry tk tv)) (n fl fc: int) (c: option (Eq.comparer tk))
              (k: tk) (i q last: int)
  : Lemma (requires search_last bs es n fl fc c k i q last /\ hit es c k i /\
                    remove_writes bs bs' es es' c k fl i last)
          (ensures wf bs' es' n i (fc + 1) c /\ fc + 1 <= n /\ 0 <= i /\ i < n /\
                   mem c (keys es n) k /\
                   removed c (keys es n) (values es n) (keys es' n) (values es' n) k (Seq.index es i).E.fld_value)
  = let o = ops tk tv in
    let vo = vops tk tv in
    hit_iff es c k i;
    HC.remove_ok o (eff c) bs bs' es es' n fl fc k i q last;
    HC.wf_count o (eff c) bs' es' n i (fc + 1);
    HC.search_found o (eff c) bs es n fl fc k i q;
    HC.fl_range o es n (-1) fl fc;
    // the values: the same unlinking, seen through the value
    HC.items_hole vo es n i;
    HC.items_hole vo es' n i;
    HC.items_frame vo es es' n i;
    HC.remove_insert (HC.items vo es n i) (HC.pos vo es i) (value_of (Seq.index es i));
    HI.pos_view o (value_of #tk #tv) es i;
    HC.items_index o es n i;
    HC.items_index vo es n i;
    HC.live_mem o (eff c) es n k i;
    remove_at_non_null (keys es n) (HC.pos o es i)
#pop-options

(* ---------------------------------------------------------------------------------- *)
(* Sizes, fresh tables *)

module HS = Pulse.Lib.CSharp.HashSize

/// Every bucket is 0: a new `int[]`.
let zeros (bs: seq I32.t) : prop =
  forall (b: nat). {:pattern Seq.index bs b} b < Seq.length bs ==> I32.v (Seq.index bs b) == 0

let wf_fresh (#tk #tv: Type0) (bs: seq I32.t) (es: seq (entry tk tv)) (c: option (Eq.comparer tk))
  : Lemma (requires Seq.length bs == Seq.length es /\ zeros bs)
          (ensures wf bs es 0 (-1) 0 c /\ keys es 0 == Seq.empty /\ values es 0 == Seq.empty)
  = HC.wf_empty (ops tk tv) (eff c) bs es

/// A table with no slots holds no key (`Remove` on a table never allocated).
let not_mem_none (#tk #tv: Type0) (es: seq (entry tk tv)) (n: int) (c: option (Eq.comparer tk)) (k: tk)
  : Lemma (n == 0 ==> ~(mem c (keys es n) k))
  = ()

(* ---------------------------------------------------------------------------------- *)
(* TryInsert *)

/// `ks'`/`vs'` are `ks`/`vs` with the pair `(k, v)` inserted at one position.
let added (#tk #tv: Type0) (ks: seq tk) (vs: seq tv) (ks': seq tk) (vs': seq tv) (k: tk) (v: tv) : prop =
  exists (p: nat). p <= Seq.length ks /\ p <= Seq.length vs /\
              ks' == HC.insert_at ks p k /\ vs' == HC.insert_at vs p v

let added_non_null (#tk #tv: Type0) (ks: seq tk) (vs: seq tv) (ks': seq tk) (vs': seq tv) (k: tk) (v: tv)
  : Lemma (requires non_null ks /\ ~(Eq.is_null k) /\ added ks vs ks' vs' k v) (ensures non_null ks')
  = eliminate exists (p: nat). p <= Seq.length ks /\ p <= Seq.length vs /\ ks' == HC.insert_at ks p k /\ vs' == HC.insert_at vs p v
    with introduce forall (j: nat). j < Seq.length ks' ==> ~(Eq.is_null (Seq.index ks' j))
         with introduce _ ==> _ with insert_at_index ks p k j

/// `vs'` is `vs` with the value of one key `c` deems equal to `k` replaced by `v`.
let overwritten (#tk #tv: Type0) (c: option (Eq.comparer tk)) (ks: seq tk) (vs vs': seq tv) (k: tk) (v: tv) : prop =
  exists (p: nat). p < Seq.length ks /\ p < Seq.length vs /\ Eq.equals (eff c) (Seq.index ks p) k /\
              vs' == Seq.upd vs p v

let fnext (#tk #tv: Type0) (es: seq (entry tk tv)) (i: int) : int = HC.fnxt (ops tk tv) es i

let insert_pre (#tk #tv: Type0) (bs: seq I32.t) (es: seq (entry tk tv)) (n fl fc: int) (c: option (Eq.comparer tk)) (k: tk)
  : Lemma (requires wf bs es n fl fc c /\ Seq.length es > 0)
          (ensures 0 <= bucket bs es c k /\ bucket bs es c k <= Seq.length es /\
                   (fc > 0 ==> 0 <= fl /\ fl < n /\ -1 <= fnext es fl /\ fnext es fl < n) /\
                   (fc == 0 ==> fl == -1) /\ fc <= n)
  = HI.insert_pre (ops tk tv) (eff c) bs es n fl fc k

/// What the code writes: entry `i` holds `(k, v)`, `(uint)` of `k`'s hash at `c` and the
/// bucket's old head, and the bucket now points at it.
let insert_writes (#tk #tv: Type0) (bs bs': seq I32.t) (es es': seq (entry tk tv)) (c: option (Eq.comparer tk))
                  (k: tk) (v: tv) (i: int) : prop =
  0 <= i /\ i < Seq.length es' /\
  (Seq.index es' i).E.fld_hashCode == Cast.int32_to_uint32 (Eq.hash (eff c) k) /\
  (Seq.index es' i).E.fld_value == v /\
  HI.insert_writes (ops tk tv) (eff c) bs bs' es es' k i

let insert_ok (#tk #tv: Type0) (bs bs': seq I32.t) (es es': seq (entry tk tv)) (n0 n1 fl1 fc1 i: int)
              (c: option (Eq.comparer tk)) (k: tk) (v: tv)
  : Lemma (requires insert_writes bs bs' es es' c k v i /\
                    ~(Eq.is_null k) /\
                    ((n1 == n0 /\ fc1 >= 0 /\ wf bs es n0 i (fc1 + 1) c /\ fl1 == fnext es i) \/
                     (fc1 == 0 /\ i == n0 /\ n1 == n0 + 1 /\ wf bs es n0 fl1 0 c)))
          (ensures wf bs' es' n1 fl1 fc1 c /\
                   added (keys es n0) (values es n0) (keys es' n1) (values es' n1) k v /\
                   Seq.length (keys es' n1) == Seq.length (keys es n0) + 1)
  = let o = ops tk tv in
    if n1 <> n0 + 1
    then HI.insert_ok o (value_of #tk #tv) (eff c) bs bs' es es' n0 i (fc1 + 1) k i n1 fl1 fc1
    else HI.insert_ok o (value_of #tk #tv) (eff c) bs bs' es es' n0 fl1 0 k i n1 fl1 fc1;
    HI.pos_view o (value_of #tk #tv) es i;
    added_non_null (keys es n0) (values es n0) (keys es' n1) (values es' n1) k v

/// `entries[i].value = v`, nothing else.
let overwrite_writes (#tk #tv: Type0) (es es': seq (entry tk tv)) (i: int) (v: tv) : prop =
  0 <= i /\ i < Seq.length es /\ Seq.length es' == Seq.length es /\
  (forall (j: nat). j < Seq.length es /\ j <> i ==> Seq.index es' j == Seq.index es j) /\
  (Seq.index es' i).E.fld_next == (Seq.index es i).E.fld_next /\
  (Seq.index es' i).E.fld_hashCode == (Seq.index es i).E.fld_hashCode /\
  (Seq.index es' i).E.fld_key == (Seq.index es i).E.fld_key /\
  (Seq.index es' i).E.fld_value == v

/// `entries[i].value = v` at the hit `i`.
let overwrite_ok (#tk #tv: Type0) (bs: seq I32.t) (es es': seq (entry tk tv)) (n fl fc: int) (c: option (Eq.comparer tk))
                 (k: tk) (v: tv) (i q: int)
  : Lemma (requires search bs es n fl fc c k i q /\ hit es c k i /\ overwrite_writes es es' i v)
          (ensures wf bs es' n fl fc c /\ keys es' n == keys es n /\
                   overwritten c (keys es n) (values es n) (values es' n) k v /\
                   mem c (keys es n) k)
  = let o = ops tk tv in
    hit_iff es c k i;
    HC.search_hit o (eff c) bs es n fl fc k i q;
    HI.overwrite_ok o (value_of #tk #tv) (eff c) bs es es' n fl fc i;
    HI.pos_view o (value_of #tk #tv) es i;
    HC.items_index o es n i

(* ---------------------------------------------------------------------------------- *)
(* Resize *)

let same_prefix (#tk #tv: Type0) (old es: seq (entry tk tv)) (n: int) : prop =
  0 <= n /\ n <= Seq.length old /\ n <= Seq.length es /\
  (forall (j: nat). {:pattern Seq.index es j} j < n ==> Seq.index es j == Seq.index old j)

let pre_wf (#tk #tv: Type0) (es: seq (entry tk tv)) (n fl fc: int) (c: option (Eq.comparer tk)) : prop =
  HI.pre_wf (ops tk tv) (eff c) es n fl fc /\ non_null (keys es n)

let copy_ok (#tk #tv: Type0) (bs: seq I32.t) (old es: seq (entry tk tv)) (n fl fc: int) (c: option (Eq.comparer tk))
  : Lemma (requires wf bs old n fl fc c /\ same_prefix old es n)
          (ensures pre_wf es n fl fc c /\ keys es n == keys old n /\ values es n == values old n)
  = HI.copy_ok (ops tk tv) (value_of #tk #tv) (eff c) bs old es n fl fc

let rebuilt (#tk #tv: Type0) (bs: seq I32.t) (src es: seq (entry tk tv)) (n i: int) : prop =
  HI.rebuilt (ops tk tv) bs src es n i /\
  (forall (j: nat). {:pattern Seq.index es j} j < Seq.length src ==> (Seq.index es j).E.fld_value == (Seq.index src j).E.fld_value)

let rebuild_start (#tk #tv: Type0) (bs: seq I32.t) (src: seq (entry tk tv)) (n: int)
  : Lemma (requires 0 <= n /\ n <= Seq.length src /\ Seq.length src > 0 /\ Seq.length bs == Seq.length src /\ zeros bs)
          (ensures rebuilt bs src src n 0)
  = HI.rebuild_start (ops tk tv) bs src n

/// The bucket of entry `i`, as stored (1-based).
let slot (#tk #tv: Type0) (bs: seq I32.t) (es: seq (entry tk tv)) (i: int) : int =
  if 0 <= i && i < Seq.length es && Seq.length bs = Seq.length es
  then I32.v (Seq.index bs (HC.bkt (hc (Seq.index es i)) (Seq.length es)))
  else 0

let rebuild_bucket (#tk #tv: Type0) (bs: seq I32.t) (src es: seq (entry tk tv)) (n i: int)
  : Lemma (requires rebuilt bs src es n i /\ i < n)
          (ensures 0 <= slot bs es i /\ slot bs es i <= Seq.length es)
  = HI.rebuild_bucket (ops tk tv) bs src es n i

/// `entries[i].next = bucket - 1; bucket = i + 1` for a live entry `i`; nothing for a dead
/// one. The value is not written.
let link_writes (#tk #tv: Type0) (bs bs': seq I32.t) (es es': seq (entry tk tv)) (i: int) : prop =
  HI.link_writes (ops tk tv) bs bs' es es' i /\
  0 <= i /\ i < Seq.length es /\ Seq.length es' == Seq.length es /\
  (Seq.index es' i).E.fld_value == (Seq.index es i).E.fld_value

let rebuild_step (#tk #tv: Type0) (bs bs': seq I32.t) (src es es': seq (entry tk tv)) (n i: int)
  : Lemma (requires rebuilt bs src es n i /\ i < n /\ link_writes bs bs' es es' i)
          (ensures rebuilt bs' src es' n (i + 1))
  = HI.rebuild_step (ops tk tv) bs bs' src es es' n i

let rebuild_done (#tk #tv: Type0) (bs: seq I32.t) (src es: seq (entry tk tv)) (n fl fc: int) (c: option (Eq.comparer tk))
  : Lemma (requires pre_wf src n fl fc c /\ rebuilt bs src es n n)
          (ensures wf bs es n fl fc c /\ keys es n == keys src n /\ values es n == values src n)
  = HI.rebuild_done (ops tk tv) (value_of #tk #tv) (eff c) bs src es n fl fc

(* ---------------------------------------------------------------------------------- *)
(* The collision path: a string-keyed dictionary switches to the randomized comparer   *)

module SC = Pulse.Lib.CSharp.StringComparers

let non_randomized (#tk: Type0) (c: option (Eq.comparer tk)) : bool =
  Some? c && SC.is_non_randomized (Some?.v c)

let randomized (#tk: Type0) (c: option (Eq.comparer tk)) : option (Eq.comparer tk) =
  match c with
  | Some h -> Some (SC.randomized h)
  | None -> None

let same_equality (#tk: Type0) (c0 c1: option (Eq.comparer tk)) : prop =
  forall (x y: tk). Eq.equals (eff c0) x y == Eq.equals (eff c1) x y

let same_refl (#tk: Type0) (c: option (Eq.comparer tk)) : Lemma (same_equality c c) = ()

let randomized_same (#tk: Type0) (c: option (Eq.comparer tk))
  : Lemma (requires non_randomized c)
          (ensures same_equality c (randomized c) /\ Some? (randomized c))
  = ()

let mem_same (#tk: Type0) (c0 c1: option (Eq.comparer tk)) (xs: seq tk) (x: tk)
  : Lemma (requires same_equality c0 c1) (ensures mem c0 xs x <==> mem c1 xs x)
  = ()

let rehashed (#tk #tv: Type0) (src es: seq (entry tk tv)) (n i: int) (c: option (Eq.comparer tk)) : prop =
  HI.rehashed (ops tk tv) (eff c) src es n i /\ non_null (keys src n) /\
  (forall (j: nat). {:pattern Seq.index es j} j < Seq.length src ==> (Seq.index es j).E.fld_value == (Seq.index src j).E.fld_value)

let rehash_start (#tk #tv: Type0) (src: seq (entry tk tv)) (n: int) (c: option (Eq.comparer tk))
  : Lemma (requires 0 <= n /\ n <= Seq.length src /\ non_null (keys src n)) (ensures rehashed src src n 0 c)
  = HI.rehash_start (ops tk tv) (eff c) src n

/// `entries[i].hashCode = (uint)comparer.GetHashCode(entries[i].key)` at a live entry `i`;
/// nothing at a dead one. The key is not null, so this is its `hash`.
let rehash_writes (#tk #tv: Type0) (es es': seq (entry tk tv)) (i: int) (c: option (Eq.comparer tk)) : prop =
  0 <= i /\ i < Seq.length es /\ Seq.length es' == Seq.length es /\
  (forall (j: nat). j < Seq.length es /\ j <> i ==> Seq.index es' j == Seq.index es j) /\
  (if I32.v (Seq.index es i).E.fld_next >= -1
   then (Seq.index es' i).E.fld_next == (Seq.index es i).E.fld_next /\
        (Seq.index es' i).E.fld_key == (Seq.index es i).E.fld_key /\
        (Seq.index es' i).E.fld_value == (Seq.index es i).E.fld_value /\
        (Seq.index es' i).E.fld_hashCode == Cast.int32_to_uint32 (Eq.get_hash_code (eff c) (Seq.index es i).E.fld_key)
   else Seq.index es' i == Seq.index es i)

let rehash_step (#tk #tv: Type0) (src es es': seq (entry tk tv)) (n i: int) (c: option (Eq.comparer tk))
  : Lemma (requires rehashed src es n i c /\ i < n /\ rehash_writes es es' i c)
          (ensures rehashed src es' n (i + 1) c)
  = if I32.v (Seq.index es i).E.fld_next >= -1 then live_non_null src n i;
    HI.rehash_step (ops tk tv) (eff c) src es es' n i

let pre_free (#tk #tv: Type0) (es: seq (entry tk tv)) (n fl fc: int) : prop =
  0 <= n /\ n <= Seq.length es /\ HC.free_ok (ops tk tv) es n (-1) fl fc

let pre_free_of (#tk #tv: Type0) (es: seq (entry tk tv)) (n fl fc: int) (c: option (Eq.comparer tk))
  : Lemma (requires pre_wf es n fl fc c) (ensures pre_free es n fl fc /\ non_null (keys es n))
  = ()

let rehash_done (#tk #tv: Type0) (src es: seq (entry tk tv)) (n fl fc: int) (c: option (Eq.comparer tk))
  : Lemma (requires pre_free src n fl fc /\ rehashed src es n n c)
          (ensures pre_wf es n fl fc c /\ keys es n == keys src n /\ values es n == values src n)
  = let o = ops tk tv in
    assert (forall (j: int). HC.dead o src n (-1) j == HC.dead o es n (-1) j);
    HC.items_frame o src es n (-1);
    HC.items_frame (vops tk tv) src es n (-1);
    HC.free_same o src es n (-1) (-1) fl fc

/// `ks'`/`vs'` are `ks`/`vs` without the pair of some key `c` deems equal to `k`.
let removed_any (#tk #tv: Type0) (c: option (Eq.comparer tk)) (ks: seq tk) (vs: seq tv) (ks': seq tk) (vs': seq tv) (k: tk) : prop =
  exists (v: tv). removed c ks vs ks' vs' k v

let removed_forget (#tk #tv: Type0) (c: option (Eq.comparer tk)) (ks: seq tk) (vs: seq tv) (ks': seq tk) (vs': seq tv) (k: tk) (v: tv)
  : Lemma (requires removed c ks vs ks' vs' k v) (ensures removed_any c ks vs ks' vs' k)
  = ()

(* ---------------------------------------------------------------------------------- *)
(* ContainsValue: a scan of the live values in entry order.                            *)
(* ---------------------------------------------------------------------------------- *)

/// `EqualityComparer<TValue>.Default.Equals(x, v)` as `ContainsValue` tests it: a null `v`
/// is compared by `x == null`.
let matches (#tv: Type0) (x v: tv) : bool =
  if Eq.is_null v then Eq.is_null x else Eq.equals (Eq.default_comparer tv) x v

let has_value (#tv: Type0) (vs: seq tv) (v: tv) : prop =
  exists (j: nat). j < Seq.length vs /\ matches (Seq.index vs j) v

let live_match (#tk #tv: Type0) (es: seq (entry tk tv)) (i: int) (v: tv) : prop =
  0 <= i /\ i < Seq.length es /\ I32.v (Seq.index es i).E.fld_next >= -1 /\
  matches (Seq.index es i).E.fld_value v

let has_value_snoc (#tv: Type0) (vs: seq tv) (x v: tv)
  : Lemma (has_value (Seq.snoc vs x) v <==> (has_value vs v \/ matches x v))
  = let s = Seq.snoc vs x in
    assert (forall (j: nat). j < Seq.length vs ==> Seq.index s j == Seq.index vs j);
    assert (Seq.index s (Seq.length vs) == x)

let has_value_step (#tk #tv: Type0) (es: seq (entry tk tv)) (i: int) (v: tv)
  : Lemma (requires 0 <= i /\ i < Seq.length es)
          (ensures has_value (values es (i + 1)) v <==> (has_value (values es i) v \/ live_match es i v))
  = if I32.v (Seq.index es i).E.fld_next >= -1
    then has_value_snoc (values es i) (Seq.index es i).E.fld_value v

let rec has_value_mono (#tk #tv: Type0) (es: seq (entry tk tv)) (i n: int) (v: tv)
  : Lemma (requires 0 <= i /\ i <= n /\ n <= Seq.length es /\ has_value (values es i) v)
          (ensures has_value (values es n) v)
          (decreases n - i)
  = if i = n then () else begin
      has_value_step es i v;
      has_value_mono es (i + 1) n v
    end

/// No live value among the first `i + 1` entries matches, given none among the first `i`
/// and entry `i` is dead or does not match.
let value_miss (#tk #tv: Type0) (es: seq (entry tk tv)) (i: int) (v: tv)
  : Lemma (requires 0 <= i /\ i < Seq.length es /\ ~(has_value (values es i) v) /\ ~(live_match es i v))
          (ensures ~(has_value (values es (i + 1)) v))
  = has_value_step es i v

/// A live matching entry `i` below `n` puts a match among the first `n` values.
let value_hit (#tk #tv: Type0) (es: seq (entry tk tv)) (i n: int) (v: tv)
  : Lemma (requires live_match es i v /\ i < n /\ n <= Seq.length es)
          (ensures has_value (values es n) v)
  = has_value_step es i v; has_value_mono es (i + 1) n v

(* ---------------------------------------------------------------------------------- *)
(* CopyTo: the live entries as key/value pairs, in entry order.                        *)
(* ---------------------------------------------------------------------------------- *)

/// `ks` and `vs` zipped: `pairs ks vs` is `KeyValuePair`s `(ks[j], vs[j])` (R29.1).
let pairs (#tk #tv: Type0) (ks: seq tk) (vs: seq tv) : seq (tk & tv) =
  if Seq.length ks = Seq.length vs
  then Seq.init (Seq.length ks) (fun j -> (Seq.index ks j, Seq.index vs j))
  else Seq.empty

let pairs_snoc (#tk #tv: Type0) (ks: seq tk) (vs: seq tv) (k: tk) (v: tv)
  : Lemma (requires Seq.length ks == Seq.length vs)
          (ensures pairs (Seq.snoc ks k) (Seq.snoc vs v) == Seq.snoc (pairs ks vs) (k, v))
  = Seq.lemma_eq_intro (pairs (Seq.snoc ks k) (Seq.snoc vs v)) (Seq.snoc (pairs ks vs) (k, v))

let pairs_slice (#tk #tv: Type0) (ks: seq tk) (vs: seq tv) (m: nat)
  : Lemma (requires Seq.length ks == Seq.length vs /\ m <= Seq.length ks)
          (ensures pairs (Seq.slice ks 0 m) (Seq.slice vs 0 m) == Seq.slice (pairs ks vs) 0 m)
  = Seq.lemma_eq_intro (pairs (Seq.slice ks 0 m) (Seq.slice vs 0 m)) (Seq.slice (pairs ks vs) 0 m)

/// The pairs of the live entries among the first `i`.
let entry_pairs (#tk #tv: Type0) (es: seq (entry tk tv)) (i: int) : seq (tk & tv) =
  pairs (keys es i) (values es i)

let pairs_length (#tk #tv: Type0) (es: seq (entry tk tv)) (i: int)
  : Lemma (Seq.length (entry_pairs es i) == Seq.length (keys es i))
  = lengths es i

let pairs_step (#tk #tv: Type0) (es: seq (entry tk tv)) (i: int)
  : Lemma (requires 0 <= i /\ i < Seq.length es)
          (ensures entry_pairs es (i + 1) ==
                   (if I32.v (Seq.index es i).E.fld_next >= -1
                    then Seq.snoc (entry_pairs es i) ((Seq.index es i).E.fld_key, (Seq.index es i).E.fld_value)
                    else entry_pairs es i))
  = lengths es i;
    if I32.v (Seq.index es i).E.fld_next >= -1
    then pairs_snoc (keys es i) (values es i) (Seq.index es i).E.fld_key (Seq.index es i).E.fld_value

let rec items_prefix (#e #k: Type0) (o: HC.ops e k) (es: seq e) (i n: nat)
  : Lemma (requires i <= n /\ n <= Seq.length es)
          (ensures Seq.length (HC.items o es i (-1)) <= Seq.length (HC.items o es n (-1)) /\
                   HC.items o es i (-1) == Seq.slice (HC.items o es n (-1)) 0 (Seq.length (HC.items o es i (-1))))
          (decreases n - i)
  = let k = Seq.length (HC.items o es i (-1)) in
    if i = n then Seq.lemma_eq_intro (HC.items o es i (-1)) (Seq.slice (HC.items o es n (-1)) 0 k)
    else begin
      items_prefix o es i (n - 1);
      Seq.lemma_eq_intro (Seq.slice (HC.items o es (n - 1) (-1)) 0 k) (Seq.slice (HC.items o es n (-1)) 0 k)
    end

/// The pairs of the live entries among the first `i` are a prefix of those among the first `n`.
let pairs_prefix (#tk #tv: Type0) (es: seq (entry tk tv)) (i n: int)
  : Lemma (requires 0 <= i /\ i <= n /\ n <= Seq.length es)
          (ensures Seq.length (entry_pairs es i) <= Seq.length (entry_pairs es n) /\
                   entry_pairs es i == Seq.slice (entry_pairs es n) 0 (Seq.length (entry_pairs es i)))
  = items_prefix (ops tk tv) es i n;
    items_prefix (vops tk tv) es i n;
    lengths es i; lengths es n;
    pairs_slice (keys es n) (values es n) (Seq.length (keys es i))

/// The live entries number the entries in use less the free ones.
let pairs_count (#tk #tv: Type0) (bs: seq I32.t) (es: seq (entry tk tv)) (n fl fc: int) (c: option (Eq.comparer tk))
  : Lemma (requires 0 <= fc /\ fc <= n /\ (n == 0 \/ wf bs es n fl fc c))
          (ensures Seq.length (entry_pairs es n) == n - fc /\ Seq.length (keys es n) == n - fc)
  = lengths es n; if n = 0 then () else HC.count_items (ops tk tv) es n (-1)

(* ---------------------------------------------------------------------------------- *)
(* Enumerators: the walk's prefixes.                                                   *)
(* ---------------------------------------------------------------------------------- *)

/// `prefixes es n` at `i` is the live pairs among the first `i` entries, `i <= n`.
let prefixes (#tk #tv: Type0) (es: seq (entry tk tv)) (n: int) : seq (seq (tk & tv)) =
  if 0 <= n && n <= Seq.length es
  then Seq.init (n + 1) (fun (i: nat{i < n + 1}) -> entry_pairs es i)
  else Seq.empty

/// The keys of a sequence of pairs.
let firsts (#tk #tv: Type0) (ps: seq (tk & tv)) : seq tk =
  Seq.init (Seq.length ps) (fun j -> fst (Seq.index ps j))

/// The values of a sequence of pairs.
let seconds (#tk #tv: Type0) (ps: seq (tk & tv)) : seq tv =
  Seq.init (Seq.length ps) (fun j -> snd (Seq.index ps j))

let firsts_snoc (#tk #tv: Type0) (ps: seq (tk & tv)) (p: tk & tv)
  : Lemma (firsts (Seq.snoc ps p) == Seq.snoc (firsts ps) (fst p))
          [SMTPat (firsts (Seq.snoc ps p))]
  = Seq.lemma_eq_intro (firsts (Seq.snoc ps p)) (Seq.snoc (firsts ps) (fst p))

let seconds_snoc (#tk #tv: Type0) (ps: seq (tk & tv)) (p: tk & tv)
  : Lemma (seconds (Seq.snoc ps p) == Seq.snoc (seconds ps) (snd p))
          [SMTPat (seconds (Seq.snoc ps p))]
  = Seq.lemma_eq_intro (seconds (Seq.snoc ps p)) (Seq.snoc (seconds ps) (snd p))

(* ---------------------------------------------------------------------------------- *)
(* KeyCollection / ValueCollection: the same walks over keys and values alone.         *)
(* ---------------------------------------------------------------------------------- *)

let keys_step (#tk #tv: Type0) (es: seq (entry tk tv)) (i: int)
  : Lemma (requires 0 <= i /\ i < Seq.length es)
          (ensures keys es (i + 1) ==
                   (if I32.v (Seq.index es i).E.fld_next >= -1
                    then Seq.snoc (keys es i) (Seq.index es i).E.fld_key
                    else keys es i))
  = ()

let values_step (#tk #tv: Type0) (es: seq (entry tk tv)) (i: int)
  : Lemma (requires 0 <= i /\ i < Seq.length es)
          (ensures values es (i + 1) ==
                   (if I32.v (Seq.index es i).E.fld_next >= -1
                    then Seq.snoc (values es i) (Seq.index es i).E.fld_value
                    else values es i))
  = ()

let keys_prefix (#tk #tv: Type0) (es: seq (entry tk tv)) (i n: int)
  : Lemma (requires 0 <= i /\ i <= n /\ n <= Seq.length es)
          (ensures Seq.length (keys es i) <= Seq.length (keys es n) /\
                   keys es i == Seq.slice (keys es n) 0 (Seq.length (keys es i)))
  = items_prefix (ops tk tv) es i n

let values_prefix (#tk #tv: Type0) (es: seq (entry tk tv)) (i n: int)
  : Lemma (requires 0 <= i /\ i <= n /\ n <= Seq.length es)
          (ensures Seq.length (values es i) <= Seq.length (values es n) /\
                   values es i == Seq.slice (values es n) 0 (Seq.length (values es i)))
  = items_prefix (vops tk tv) es i n

/// The keys and values of the pairs of the live entries are the live keys and values.
let firsts_pairs (#tk #tv: Type0) (es: seq (entry tk tv)) (i: int)
  : Lemma (firsts (entry_pairs es i) == keys es i /\ seconds (entry_pairs es i) == values es i)
  = lengths es i;
    Seq.lemma_eq_intro (firsts (entry_pairs es i)) (keys es i);
    Seq.lemma_eq_intro (seconds (entry_pairs es i)) (values es i)

(* ---------------------------------------------------------------------------------- *)
(* The bucket index of `(uint)hashCode % buckets.Length`, computed in `long`.          *)
(* ---------------------------------------------------------------------------------- *)

let div_fits (a b: int)
  : Lemma (requires 0 <= a /\ 0 < b) (ensures 0 <= a / b /\ a / b <= a)
  = FStar.Math.Lemmas.lemma_mult_le_left a 1 b;
    FStar.Math.Lemmas.lemma_div_le a (a * b) b;
    FStar.Math.Lemmas.cancel_mul_div a b;
    FStar.Math.Lemmas.lemma_div_le 0 a b

(* ---------------------------------------------------------------------------------- *)
(* The constructors (R30.28)                                                         *)

/// An empty table is well formed at any comparer: only live entries' hashes depend on it.
let wf_rebind (#tk #tv: Type0) (bs: seq I32.t) (es: seq (entry tk tv)) (fl: int) (c c2: option (Eq.comparer tk))
  : Lemma (wf bs es 0 fl 0 c ==> wf bs es 0 fl 0 c2)
  = ()

module SCO = Pulse.Lib.CSharp.StringComparerOf
module Obj = Pulse.Lib.CSharp.Obj

/// `_comparer = (IEqualityComparer<TKey>)stringComparer` keeps the dictionary's equality,
/// when `stringComparer` is what `GetStringComparer(_comparer)` gave back for string keys.
let string_swap_ok (#t: Type0) (c: option (Eq.comparer t)) : prop =
  (Eq.type_of t == Eq.type_of string /\ Some? c /\ Some? (SCO.string_comparer (Obj.box #(option (Eq.comparer t)) c)))
  ==> same_equality c (Some (Some?.v (SCO.string_comparer (Obj.box #(option (Eq.comparer t)) c))))

let string_swap (#t: Type0) (c: option (Eq.comparer t)) : Lemma (string_swap_ok c) =
  match c, SCO.string_comparer (Obj.box #(option (Eq.comparer t)) c) with
  | Some c', Some h ->
    let step (x y: t)
      : Lemma (Eq.type_of t == Eq.type_of string ==> Eq.equals (eff c) x y == Eq.equals (eff #t (Some h)) x y) =
      FStar.Classical.move_requires (SCO.string_comparer_equals #t c' h x) y in
    FStar.Classical.forall_intro_2 step
  | _ -> ()

(* ---------------------------------------------------------------------------------- *)
(* Compacting into new arrays: `CopyEntries` (TrimExcess)                             *)

/// What `CopyEntries` needs of the old entries once their buckets are gone: their live
/// entries' hashes are right and their keys are not null.
let compactable (#tk #tv: Type0) (old: seq (entry tk tv)) (n: int) (c: option (Eq.comparer tk)) : prop =
  0 <= n /\ n <= Seq.length old /\ HC.hashes_ok (ops tk tv) (eff c) old n (-1) /\ non_null (keys old n)

let wf_compactable (#tk #tv: Type0) (bs: seq I32.t) (old: seq (entry tk tv)) (n fl fc: int) (c: option (Eq.comparer tk))
  : Lemma (requires wf bs old n fl fc c /\ 0 <= fc /\ fc <= n)
          (ensures compactable old n c /\ Seq.length (keys old n) == n - fc)
  = pairs_count bs old n fl fc c

let compacted (#tk #tv: Type0) (bs: seq I32.t) (old es: seq (entry tk tv)) (n i m: int) (c: option (Eq.comparer tk)) : prop =
  HI.compacted (ops tk tv) (value_of #tk #tv) (eff c) bs old es n i m /\
  non_null (keys old n) /\ Seq.length (keys old n) <= Seq.length es

let compact_start (#tk #tv: Type0) (bs: seq I32.t) (old es: seq (entry tk tv)) (n: int) (c: option (Eq.comparer tk))
  : Lemma (requires compactable old n c /\ Seq.length es > 0 /\ Seq.length bs == Seq.length es /\ zeros bs /\
                    Seq.length (keys old n) <= Seq.length es)
          (ensures compacted bs old es n 0 0 c)
  = HI.compact_start (ops tk tv) (value_of #tk #tv) (eff c) bs old es n

/// The slot `old[i]` goes to in `es`'s buckets.
let old_slot (#tk #tv: Type0) (bs: seq I32.t) (old es: seq (entry tk tv)) (i: int) : int =
  if 0 <= i && i < Seq.length old && Seq.length bs = Seq.length es && Seq.length es > 0
  then I32.v (Seq.index bs (HC.bkt (hc (Seq.index old i)) (Seq.length es)))
  else 0

let compact_room (#tk #tv: Type0) (bs: seq I32.t) (old es: seq (entry tk tv)) (n i m: int) (c: option (Eq.comparer tk))
  : Lemma (requires compacted bs old es n i m c /\ i < n /\ I32.v (Seq.index old i).E.fld_next >= -1)
          (ensures m < Seq.length es /\ 0 <= m /\ 0 <= old_slot bs old es i /\ old_slot bs old es i <= Seq.length es)
  = HI.compact_room (ops tk tv) (value_of #tk #tv) (eff c) bs old es n i m

/// What the step at `old[i]` wrote: when it is live, it is copied (value too) to `es[m]`,
/// linked at the head of its bucket, and `m` grew by one; otherwise nothing.
let compact_writes (#tk #tv: Type0) (bs bs': seq I32.t) (old es es': seq (entry tk tv)) (i m m': int) : prop =
  0 <= i /\ i < Seq.length old /\
  (if I32.v (Seq.index old i).E.fld_next >= -1
   then HI.copy_writes (ops tk tv) bs bs' old es es' i m /\
        (Seq.index es' m).E.fld_value == (Seq.index old i).E.fld_value /\ m' == m + 1
   else es' == es /\ bs' == bs /\ m' == m)

let compact_step (#tk #tv: Type0) (bs bs': seq I32.t) (old es es': seq (entry tk tv)) (n i m m': int) (c: option (Eq.comparer tk))
  : Lemma (requires compacted bs old es n i m c /\ i < n /\ compact_writes bs bs' old es es' i m m')
          (ensures compacted bs' old es' n (i + 1) m' c)
  = HI.compact_step (ops tk tv) (value_of #tk #tv) (eff c) bs bs' old es es' n i m

let compact_done (#tk #tv: Type0) (bs: seq I32.t) (old es: seq (entry tk tv)) (n m: int) (c: option (Eq.comparer tk))
  : Lemma (requires compacted bs old es n n m c)
          (ensures wf bs es m (-1) 0 c /\ keys es m == keys old n /\ values es m == values old n /\
                   m <= Seq.length es /\ Seq.length (keys es m) == m)
  = HI.compact_done (ops tk tv) (value_of #tk #tv) (eff c) bs old es n m;
    pairs_count bs es m (-1) 0 c
