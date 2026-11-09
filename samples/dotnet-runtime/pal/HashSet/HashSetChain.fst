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
