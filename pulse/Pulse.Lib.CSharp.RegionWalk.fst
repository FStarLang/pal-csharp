module Pulse.Lib.CSharp.RegionWalk

/// R27.35. An in-order walk of a region's tree that keeps a stack of pointers into the
/// region: `SortedSet<T>`'s enumerator and `InOrderTreeWalk`. The stack is an ordinary
/// sequence of boxes; what it means is a pure function of the heap the owner holds.
///
/// * `okeys rev t` is the keys of `t` in order, or in reverse order when `rev`.
/// * `entry` is what one pushed node still owes: its key, then the keys on its far side.
/// * `pending h s` is everything the stack still owes, top (the last element) first.
/// * `walkable h s`: every pointer on the stack is non-null and well-formed in `h`.
///
/// Every definition takes the region class's view and links first (`[RegionOp]`, R27.22).
/// Nothing here is trusted beyond `Pulse.Lib.CSharp.RefEq.ref_eq` (R27.8).

open Pulse.Lib.CSharp.Region
module B = Pulse.Lib.Box
module T = Pulse.Lib.CSharp.Tree
module ST = Pulse.Lib.CSharp.SearchTree
module CS = Pulse.Lib.CSharp.Seq
module Seq = FStar.Seq

let rec okeys (#a #b: Type0) (rev: bool) (t: T.tree (a & b)) : Tot (Seq.seq a) (decreases t) =
  match t with
  | T.Leaf -> Seq.empty
  | T.Branch l (k, _) r ->
    if rev then Seq.append (okeys rev r) (Seq.cons k (okeys rev l))
    else Seq.append (okeys rev l) (Seq.cons k (okeys rev r))

let rec okeys_length (#a #b: Type0) (rev: bool) (t: T.tree (a & b))
  : Lemma (ensures Seq.length (okeys rev t) == T.size t) (decreases t)
          [SMTPat (Seq.length (okeys rev t))]
  = match t with
    | T.Leaf -> ()
    | T.Branch l _ r -> okeys_length rev l; okeys_length rev r

let rec okeys_fwd (#a #b: Type0) (t: T.tree (a & b))
  : Lemma (ensures okeys false t == ST.keys t) (decreases t) [SMTPat (okeys false t)]
  = match t with
    | T.Leaf -> ()
    | T.Branch l _ r -> okeys_fwd l; okeys_fwd r

let reverse_append3 (#a: Type0) (x: Seq.seq a) (k: a) (y: Seq.seq a)
  : Lemma (CS.reverse_all (Seq.append x (Seq.cons k y)) ==
           Seq.append (CS.reverse_all y) (Seq.cons k (CS.reverse_all x)))
  = Seq.lemma_eq_intro (CS.reverse_all (Seq.append x (Seq.cons k y)))
                       (Seq.append (CS.reverse_all y) (Seq.cons k (CS.reverse_all x)))

let rec okeys_rev (#a #b: Type0) (t: T.tree (a & b))
  : Lemma (ensures okeys true t == CS.reverse_all (ST.keys t)) (decreases t) [SMTPat (okeys true t)]
  = match t with
    | T.Leaf -> Seq.lemma_eq_intro (okeys true t) (CS.reverse_all (ST.keys t))
    | T.Branch l (k, _) r -> okeys_rev l; okeys_rev r; reverse_append3 (ST.keys l) k (ST.keys r)

/// The side a walk descends first: left in order, right in reverse.
let near (#r: Type0) (left right: r -> B.box r) (rev: bool) (v: r) : B.box r =
  if rev then right v else left v

/// The side a popped node's successors are on.
let far (#r: Type0) (left right: r -> B.box r) (rev: bool) (v: r) : B.box r =
  if rev then left v else right v

let entry (#r #a #b: Type0) (view: B.box r -> r -> (a & b)) (left right: r -> B.box r)
    (rev: bool) (h: heap r) (x: B.box r) : GTot (Seq.seq a) =
  match tree_of view left right h x with
  | T.Leaf -> Seq.empty
  | T.Branch l (k, _) rt -> Seq.cons k (okeys rev (if rev then l else rt))

let rec pending (#r #a #b: Type0) (view: B.box r -> r -> (a & b)) (left right: r -> B.box r)
    (rev: bool) (h: heap r) (s: Seq.seq (B.box r)) : GTot (Seq.seq a) (decreases Seq.length s) =
  if Seq.length s = 0 then Seq.empty
  else
    let n = Seq.length s - 1 in
    Seq.append (entry view left right rev h (Seq.index s n))
               (pending view left right rev h (Seq.slice s 0 n))

let walkable (#r #a #b: Type0) (view: B.box r -> r -> (a & b)) (left right: r -> B.box r)
    (h: heap r) (s: Seq.seq (B.box r)) : prop =
  forall (i: nat). {:pattern Seq.index s i}
    i < Seq.length s ==> wf left right h (Seq.index s i) /\ not (B.is_null (Seq.index s i))

let pending_empty (#r #a #b: Type0) (view: B.box r -> r -> (a & b)) (left right: r -> B.box r)
    (rev: bool) (h: heap r) (s: Seq.seq (B.box r))
  : Lemma (requires Seq.length s == 0)
          (ensures pending view left right rev h s == Seq.empty /\ walkable view left right h s)
  = ()

let pending_push (#r #a #b: Type0) (view: B.box r -> r -> (a & b)) (left right: r -> B.box r)
    (rev: bool) (h: heap r) (s: Seq.seq (B.box r)) (x: B.box r)
  : Lemma (pending view left right rev h (Seq.snoc s x) ==
           Seq.append (entry view left right rev h x) (pending view left right rev h s))
  = Seq.lemma_eq_intro (Seq.slice (Seq.snoc s x) 0 (Seq.length s)) s

/// A walkable stack owes at least one key per pointer.
let rec walkable_length (#r #a #b: Type0) (view: B.box r -> r -> (a & b)) (left right: r -> B.box r)
    (rev: bool) (h: heap r) (s: Seq.seq (B.box r))
  : Lemma (requires walkable view left right h s)
          (ensures Seq.length s <= Seq.length (pending view left right rev h s))
          (decreases Seq.length s)
  = if Seq.length s = 0 then ()
    else begin
      let n = Seq.length s - 1 in
      wf_step view left right h (Seq.index s n);
      walkable_length view left right rev h (Seq.slice s 0 n)
    end

/// The walk's descent, one node: pushing a well-formed `x` and moving to its near child
/// keeps what is still owed.
let descend (#r #a #b: Type0) (view: B.box r -> r -> (a & b)) (left right: r -> B.box r)
    (rev: bool) (h: heap r) (s: Seq.seq (B.box r)) (x: B.box r)
  : Lemma (requires wf left right h x /\ not (B.is_null x) /\ walkable view left right h s)
          (ensures mem h x /\ T.Branch? (tree_of view left right h x) /\
                   Seq.length s < Seq.length (okeys rev (tree_of view left right h x)) +
                                  Seq.length (pending view left right rev h s) /\
                   Seq.length s < Seq.length (Seq.append (okeys rev (tree_of view left right h x))
                                                         (pending view left right rev h s)) /\
                   wf left right h (near left right rev (get h x)) /\
                   walkable view left right h (Seq.snoc s x) /\
                   Seq.length (okeys rev (tree_of view left right h x)) + Seq.length (pending view left right rev h s) ==
                   Seq.length (okeys rev (tree_of view left right h (near left right rev (get h x)))) +
                   Seq.length (pending view left right rev h (Seq.snoc s x)) /\
                   Seq.append (okeys rev (tree_of view left right h x)) (pending view left right rev h s) ==
                   Seq.append (okeys rev (tree_of view left right h (near left right rev (get h x))))
                              (pending view left right rev h (Seq.snoc s x)))
  = wf_step view left right h x;
    walkable_length view left right rev h s;
    pending_push view left right rev h s x;
    let T.Branch l (k, _) rt = tree_of view left right h x in
    if rev then
      Seq.append_assoc (okeys rev rt) (Seq.cons k (okeys rev l)) (pending view left right rev h s)
    else
      Seq.append_assoc (okeys rev l) (Seq.cons k (okeys rev rt)) (pending view left right rev h s)

/// The walk's pop: the top `x` owes its key, then its far side, then the rest.
let pop (#r #a #b: Type0) (view: B.box r -> r -> (a & b)) (left right: r -> B.box r)
    (rev: bool) (h: heap r) (s: Seq.seq (B.box r))
  : Lemma (requires Seq.length s > 0 /\ walkable view left right h s)
          (ensures (let n = Seq.length s - 1 in
                    let x = Seq.index s n in
                    mem h x /\ not (B.is_null x) /\
                    walkable view left right h (Seq.slice s 0 n) /\
                    wf left right h (far left right rev (get h x)) /\
                    Seq.length (pending view left right rev h s) ==
                    1 + Seq.length (okeys rev (tree_of view left right h (far left right rev (get h x)))) +
                        Seq.length (pending view left right rev h (Seq.slice s 0 n)) /\
                    pending view left right rev h s ==
                    Seq.cons (fst (view x (get h x)))
                             (Seq.append (okeys rev (tree_of view left right h (far left right rev (get h x))))
                                         (pending view left right rev h (Seq.slice s 0 n)))))
  = let n = Seq.length s - 1 in
    let x = Seq.index s n in
    wf_step view left right h x;
    let T.Branch l (k, _) rt = tree_of view left right h x in
    let rest = pending view left right rev h (Seq.slice s 0 n) in
    let o = okeys rev (if rev then l else rt) in
    Seq.lemma_eq_intro (Seq.append (Seq.cons k o) rest) (Seq.cons k (Seq.append o rest))


/// `pop`, for a stack that owes the window `ks[n..]` of a sequence: the top's key is `ks[n]`,
/// and what is left is owed `ks[n+1..]`.
let pop_at (#r #a #b: Type0) (view: B.box r -> r -> (a & b)) (left right: r -> B.box r)
    (rev: bool) (h: heap r) (s: Seq.seq (B.box r)) (ks: Seq.seq a) (n: int)
  : Lemma (requires Seq.length s > 0 /\ walkable view left right h s /\ 0 <= n /\ n <= Seq.length ks /\
                    pending view left right rev h s == Seq.slice ks n (Seq.length ks))
          (ensures (let m = Seq.length s - 1 in
                    let x = Seq.index s m in
                    mem h x /\ not (B.is_null x) /\ n < Seq.length ks /\
                    walkable view left right h (Seq.slice s 0 m) /\
                    wf left right h (far left right rev (get h x)) /\
                    fst (view x (get h x)) == Seq.index ks n /\
                    Seq.append (okeys rev (tree_of view left right h (far left right rev (get h x))))
                               (pending view left right rev h (Seq.slice s 0 m)) ==
                    Seq.slice ks (n + 1) (Seq.length ks)))
  = pop view left right rev h s;
    let m = Seq.length s - 1 in
    let x = Seq.index s m in
    let rest = Seq.append (okeys rev (tree_of view left right h (far left right rev (get h x))))
                          (pending view left right rev h (Seq.slice s 0 m)) in
    let k = fst (view x (get h x)) in
    let w = Seq.slice ks n (Seq.length ks) in
    assert (Seq.index w 0 == Seq.index ks n);
    let aux (i: nat { i < Seq.length rest })
      : Lemma (Seq.index rest i == Seq.index (Seq.slice ks (n + 1) (Seq.length ks)) i)
      = assert (Seq.index (Seq.cons k rest) (i + 1) == Seq.index rest i);
        assert (Seq.index w (i + 1) == Seq.index ks (n + 1 + i))
    in
    FStar.Classical.forall_intro aux;
    Seq.lemma_eq_intro rest (Seq.slice ks (n + 1) (Seq.length ks))

/// R27.39. The trace of a walk's callback: each entry is the view of the node it was called
/// on and what it returned; `tkey` is the node's key.
let tkey (#a #b #c: Type0) (e: (a & b) & c) : a = fst (fst e)

/// The callback has been called on `keys[0..|tr|)`, in order, and returned true each time.
let visited (#a #b: Type0) (keys: Seq.seq a) (tr: Seq.seq ((a & b) & bool)) : prop =
  Seq.length tr <= Seq.length keys /\
  (forall (i: nat). {:pattern Seq.index tr i} i < Seq.length tr ==> tkey (Seq.index tr i) == Seq.index keys i /\ snd (Seq.index tr i) == true)

/// A walk over `keys` that returned `res`: the callback was called on a prefix of `keys`, in
/// order; it returned true on all but possibly the last call; and the walk returned true
/// exactly when it went through all of `keys`, false when the last call returned false.
let walked (#a #b: Type0) (keys: Seq.seq a) (tr: Seq.seq ((a & b) & bool)) (res: bool) : prop =
  Seq.length tr <= Seq.length keys /\
  (forall (i: nat). {:pattern Seq.index tr i} i < Seq.length tr ==> tkey (Seq.index tr i) == Seq.index keys i) /\
  (forall (i: nat). {:pattern Seq.index tr i} i + 1 < Seq.length tr ==> snd (Seq.index tr i) == true) /\
  (res == true ==> Seq.length tr == Seq.length keys /\ (forall (i: nat). {:pattern Seq.index tr i} i < Seq.length tr ==> snd (Seq.index tr i) == true)) /\
  (res == false ==> Seq.length tr > 0 /\ snd (Seq.index tr (Seq.length tr - 1)) == false)

let visited_empty (#a #b: Type0) (keys: Seq.seq a)
  : Lemma (visited #a #b keys Seq.empty)
          [SMTPat (visited #a #b keys Seq.empty)]
  = ()

/// One more call, on the next key: a true result extends the visit, a false one ends the walk.
let visited_snoc (#a #b: Type0) (keys: Seq.seq a) (tr: Seq.seq ((a & b) & bool)) (e: (a & b) & bool)
  : Lemma (requires visited keys tr /\ Seq.length tr < Seq.length keys /\ tkey e == Seq.index keys (Seq.length tr))
          (ensures (snd e == true ==> visited keys (Seq.snoc tr e)) /\
                   (snd e == false ==> walked keys (Seq.snoc tr e) false))
          [SMTPatOr [[SMTPat (visited keys (Seq.snoc tr e))]; [SMTPat (walked keys (Seq.snoc tr e) false)]]]
  = let tr' = Seq.snoc tr e in
    assert (forall (i: nat). i < Seq.length tr ==> Seq.index tr' i == Seq.index tr i);
    assert (Seq.index tr' (Seq.length tr) == e)

/// A visit of every key is a walk that returned true.
let visited_all (#a #b: Type0) (keys: Seq.seq a) (tr: Seq.seq ((a & b) & bool))
  : Lemma (requires visited keys tr /\ Seq.length tr == Seq.length keys)
          (ensures walked keys tr true)
          [SMTPat (walked keys tr true)]
  = ()

let imin (x y: int) : int = if x <= y then x else y

/// R27.39. The protocol of a callback copying keys into `a` from `i0` up to `hi`, starting
/// from contents `a0`, now at `idx`: it copied the first `min(|tr|, hi - i0)` keys it was
/// called on, and returned true exactly on the calls that copied.
let copied (#t #b: Type0) (tr: Seq.seq ((t & b) & bool)) (a0 a: Seq.seq t) (i0 hi idx: int) : prop =
  0 <= i0 /\ i0 <= hi /\ hi <= Seq.length a0 /\ Seq.length a == Seq.length a0 /\
  idx - i0 == imin (Seq.length tr) (hi - i0) /\
  (forall (k: nat). k < Seq.length tr ==> snd (Seq.index tr k) == (i0 + k < hi)) /\
  (forall (j: nat). j < Seq.length a ==>
     Seq.index a j == (if i0 <= j && j < idx then tkey (Seq.index tr (j - i0)) else Seq.index a0 j))

/// What a copy leaves: `a` is `a0` with the first `min(|keys|, hi - i0)` keys at `i0`.
let copy_result (#t: Type0) (keys a0 a: Seq.seq t) (i0 hi: int) : prop =
  0 <= i0 /\ Seq.length a == Seq.length a0 /\
  (forall (j: nat). j < Seq.length a ==>
     Seq.index a j == (if i0 <= j && j < i0 + imin (Seq.length keys) (hi - i0)
                       then Seq.index keys (j - i0) else Seq.index a0 j))

let copied_walked (#t #b: Type0) (keys: Seq.seq t) (tr: Seq.seq ((t & b) & bool)) (res: bool)
    (a0 a: Seq.seq t) (i0 hi idx: int)
  : Lemma (requires walked keys tr res /\ copied tr a0 a i0 hi idx)
          (ensures copy_result keys a0 a i0 hi)
          [SMTPat (walked keys tr res); SMTPat (copied tr a0 a i0 hi idx)]
  = if res then ()
    else begin
      let n = Seq.length tr in
      assert (snd (Seq.index tr (n - 1)) == false);
      if n >= 2 then assert (snd (Seq.index tr (n - 2)) == true)
    end

/// A copy of every key is a splice of the keys into the array.
let copy_result_splice (#t: Type0) (keys a0 a: Seq.seq t) (i0 hi: int)
  : Lemma (requires copy_result keys a0 a i0 hi /\ hi == i0 + Seq.length keys /\ hi <= Seq.length a0)
          (ensures a == CS.splice a0 i0 hi keys)
          [SMTPat (copy_result keys a0 a i0 hi)]
  = Seq.lemma_eq_intro a (CS.splice a0 i0 hi keys)

(* ------------------------------------------------------------------------------------ *)
(* R27.40. A breadth-first walk, over a queue of pointers into the region               *)

module SF = Pulse.Lib.CSharp.SetFilter

/// Everything the queue `q` still owes: the keys of each queued node's tree, front first.
let rec bpending (#r #a #b: Type0) (view: B.box r -> r -> (a & b)) (left right: r -> B.box r)
    (h: heap r) (q: Seq.seq (B.box r)) : GTot (Seq.seq a) (decreases Seq.length q) =
  if Seq.length q = 0 then Seq.empty
  else
    let n = Seq.length q - 1 in
    Seq.append (bpending view left right h (Seq.slice q 0 n))
               (okeys false (tree_of view left right h (Seq.index q n)))

let bpending_snoc (#r #a #b: Type0) (view: B.box r -> r -> (a & b)) (left right: r -> B.box r)
    (h: heap r) (q: Seq.seq (B.box r)) (x: B.box r)
  : Lemma (bpending view left right h (Seq.snoc q x) ==
           Seq.append (bpending view left right h q) (okeys false (tree_of view left right h x)))
          [SMTPat (bpending view left right h (Seq.snoc q x))]
  = Seq.lemma_eq_intro (Seq.slice (Seq.snoc q x) 0 (Seq.length q)) q

let walkable_snoc (#r #a #b: Type0) (view: B.box r -> r -> (a & b)) (left right: r -> B.box r)
    (h: heap r) (q: Seq.seq (B.box r)) (x: B.box r)
  : Lemma (requires walkable view left right h q /\ wf left right h x /\ not (B.is_null x))
          (ensures walkable view left right h (Seq.snoc q x))
          [SMTPat (walkable view left right h (Seq.snoc q x))]
  = ()

let rec bpending_front (#r #a #b: Type0) (view: B.box r -> r -> (a & b)) (left right: r -> B.box r)
    (h: heap r) (q: Seq.seq (B.box r))
  : Lemma (requires Seq.length q > 0)
          (ensures bpending view left right h q ==
                   Seq.append (okeys false (tree_of view left right h (Seq.index q 0)))
                              (bpending view left right h (Seq.slice q 1 (Seq.length q))))
          (decreases Seq.length q)
  = let n = Seq.length q - 1 in
    let t0 = okeys false (tree_of view left right h (Seq.index q 0)) in
    if n = 0 then begin
      Seq.lemma_eq_intro (bpending view left right h q) (Seq.append t0 Seq.empty)
    end else begin
      let init = Seq.slice q 0 n in
      bpending_front view left right h init;
      let tl = Seq.slice q 1 (Seq.length q) in
      Seq.lemma_eq_intro (Seq.slice init 1 n) (Seq.slice tl 0 (n - 1));
      assert (Seq.index tl (n - 1) == Seq.index q n);
      Seq.append_assoc t0 (bpending view left right h (Seq.slice init 1 n))
                       (okeys false (tree_of view left right h (Seq.index q n)))
    end

/// A walkable queue owes at least one key per pointer.
let rec bwalkable_length (#r #a #b: Type0) (view: B.box r -> r -> (a & b)) (left right: r -> B.box r)
    (h: heap r) (q: Seq.seq (B.box r))
  : Lemma (requires walkable view left right h q)
          (ensures Seq.length q <= Seq.length (bpending view left right h q))
          (decreases Seq.length q)
  = if Seq.length q = 0 then ()
    else begin
      let n = Seq.length q - 1 in
      wf_step view left right h (Seq.index q n);
      bwalkable_length view left right h (Seq.slice q 0 n)
    end

/// The walk's dequeue: the front `x` is a node whose tree owes its left keys, its key and
/// its right keys, before what the rest of the queue owes.
let bf_front (#r #a #b: Type0) (view: B.box r -> r -> (a & b)) (left right: r -> B.box r)
    (h: heap r) (q: Seq.seq (B.box r))
  : Lemma (requires Seq.length q > 0 /\ walkable view left right h q)
          (ensures (let x = Seq.index q 0 in
                    let rest = Seq.slice q 1 (Seq.length q) in
                    mem h x /\ not (B.is_null x) /\
                    wf left right h (left (get h x)) /\ wf left right h (right (get h x)) /\
                    walkable view left right h rest /\
                    Seq.length rest <= Seq.length (bpending view left right h rest) /\
                    bpending view left right h q ==
                    Seq.append (Seq.append (okeys false (tree_of view left right h (left (get h x))))
                                           (Seq.cons (fst (view x (get h x)))
                                                     (okeys false (tree_of view left right h (right (get h x))))))
                               (bpending view left right h rest)))
  = let x = Seq.index q 0 in
    let rest = Seq.slice q 1 (Seq.length q) in
    wf_step view left right h x;
    bpending_front view left right h q;
    bwalkable_length view left right h rest

/// Some call in the trace was on a node with key `y`.
let in_trace (#a #b #c: Type0) (tr: Seq.seq ((a & b) & c)) (y: a) : prop =
  exists (i: nat). i < Seq.length tr /\ tkey (Seq.index tr i) == y

let in_trace_empty (#a #b #c: Type0) (y: a)
  : Lemma (~(in_trace (Seq.empty #((a & b) & c)) y))
          [SMTPat (in_trace (Seq.empty #((a & b) & c)) y)]
  = ()

let in_trace_snoc (#a #b #c: Type0) (tr: Seq.seq ((a & b) & c)) (e: (a & b) & c) (y: a)
  : Lemma (in_trace (Seq.snoc tr e) y <==> in_trace tr y \/ tkey e == y)
          [SMTPat (in_trace (Seq.snoc tr e) y)]
  = let tr' = Seq.snoc tr e in
    let fwd (i: nat) : Lemma (requires i < Seq.length tr' /\ tkey (Seq.index tr' i) == y)
                             (ensures in_trace tr y \/ tkey e == y)
      = if i < Seq.length tr then assert (tkey (Seq.index tr i) == y) else () in
    let bwd (i: nat) : Lemma (requires i < Seq.length tr /\ tkey (Seq.index tr i) == y)
                             (ensures in_trace tr' y)
      = assert (Seq.index tr' i == Seq.index tr i) in
    FStar.Classical.forall_intro (FStar.Classical.move_requires fwd);
    FStar.Classical.forall_intro (FStar.Classical.move_requires bwd);
    assert (Seq.index tr' (Seq.length tr) == e)

/// A breadth-first walk over `keys` that has called the callback once per key it took off
/// the queue, each call returning true, with `pend` owed: between them, the trace and what
/// is owed account for every key, once.
[@@"opaque_to_smt"]
let bf_visited (#a #b: Type0) (keys: Seq.seq a) (tr: Seq.seq ((a & b) & bool)) (pend: Seq.seq a) : prop =
  Seq.length tr + Seq.length pend == Seq.length keys /\
  (forall (i: nat). i < Seq.length tr ==> snd (Seq.index tr i) == true /\ SF.contains keys (tkey (Seq.index tr i))) /\
  (forall (y: a). {:pattern SF.contains pend y} SF.contains pend y ==> SF.contains keys y) /\
  (forall (y: a). {:pattern SF.contains keys y} SF.contains keys y ==> in_trace tr y \/ SF.contains pend y)

/// A breadth-first walk over `keys` that returned `res`: the callback was called only on
/// keys; it returned true on all but possibly the last call; the walk returned true when
/// every call did and every key was called on, false when the last call returned false.
[@@"opaque_to_smt"]
let bf_walked (#a #b: Type0) (keys: Seq.seq a) (tr: Seq.seq ((a & b) & bool)) (res: bool) : prop =
  Seq.length tr <= Seq.length keys /\
  (forall (i: nat). i < Seq.length tr ==> SF.contains keys (tkey (Seq.index tr i))) /\
  (forall (i: nat). i + 1 < Seq.length tr ==> snd (Seq.index tr i) == true) /\
  (res == true ==> (forall (i: nat). i < Seq.length tr ==> snd (Seq.index tr i) == true) /\
                   (forall (y: a). SF.contains keys y ==> in_trace tr y)) /\
  (res == false ==> Seq.length tr > 0 /\ snd (Seq.index tr (Seq.length tr - 1)) == false)

/// Taking the front off and calling the callback on it: a true result keeps the visit,
/// with the front's children owed after the rest of the queue; a false one ends the walk.
let bf_step (#a #b: Type0) (keys: Seq.seq a) (tr: Seq.seq ((a & b) & bool))
    (l: Seq.seq a) (k: a) (rt rest: Seq.seq a) (e: (a & b) & bool)
  : Lemma (requires bf_visited keys tr (Seq.append (Seq.append l (Seq.cons k rt)) rest) /\ tkey e == k)
          (ensures Seq.length tr < Seq.length keys /\
                   (snd e == true ==> bf_visited keys (Seq.snoc tr e) (Seq.append (Seq.append rest l) rt)) /\
                   (snd e == false ==> bf_walked keys (Seq.snoc tr e) false))
          [SMTPat (bf_visited keys tr (Seq.append (Seq.append l (Seq.cons k rt)) rest)); SMTPat (Seq.snoc tr e)]
  = reveal_opaque (`%bf_visited) (bf_visited #a #b);
    reveal_opaque (`%bf_walked) (bf_walked #a #b);
    let tr' = Seq.snoc tr e in
    let pend = Seq.append (Seq.append l (Seq.cons k rt)) rest in
    let pend' = Seq.append (Seq.append rest l) rt in
    SF.contains_append (Seq.append l (Seq.cons k rt)) rest k;
    SF.contains_append l (Seq.cons k rt) k;
    SF.contains_cons k rt k;
    assert (SF.contains keys k);
    let idx (i: nat { i < Seq.length tr' })
      : Lemma (Seq.index tr' i == (if i < Seq.length tr then Seq.index tr i else e))
      = () in
    FStar.Classical.forall_intro idx;
    let mem_pend (y: a)
      : Lemma ((SF.contains pend y <==> SF.contains l y \/ k == y \/ SF.contains rt y \/ SF.contains rest y) /\
               (SF.contains pend' y <==> SF.contains l y \/ SF.contains rt y \/ SF.contains rest y))
      = SF.contains_append (Seq.append l (Seq.cons k rt)) rest y;
        SF.contains_append l (Seq.cons k rt) y;
        SF.contains_cons k rt y;
        SF.contains_append (Seq.append rest l) rt y;
        SF.contains_append rest l y in
    FStar.Classical.forall_intro mem_pend;
    FStar.Classical.forall_intro (in_trace_snoc tr e);
    if snd e then begin
      assert (Seq.length tr' + Seq.length pend' == Seq.length keys);
      assert (forall (i: nat). i < Seq.length tr' ==> snd (Seq.index tr' i) == true /\ SF.contains keys (tkey (Seq.index tr' i)));
      assert (forall (y: a). SF.contains pend' y ==> SF.contains keys y);
      assert (forall (y: a). SF.contains keys y ==> in_trace tr' y \/ SF.contains pend' y)
    end else begin
      assert (forall (i: nat). i < Seq.length tr' ==> SF.contains keys (tkey (Seq.index tr' i)))
    end

let bf_visited_done (#a #b: Type0) (keys: Seq.seq a) (tr: Seq.seq ((a & b) & bool)) (pend: Seq.seq a)
  : Lemma (requires bf_visited keys tr pend /\ Seq.length pend == 0)
          (ensures bf_walked keys tr true)
          [SMTPat (bf_visited keys tr pend); SMTPat (bf_walked keys tr true)]
  = reveal_opaque (`%bf_visited) (bf_visited #a #b);
    reveal_opaque (`%bf_walked) (bf_walked #a #b);
    assert (forall (y: a). ~(SF.contains pend y))

/// The walk's start: no calls yet, and a queue that owes every key.
let bf_start (#r #a #b: Type0) (view: B.box r -> r -> (a & b)) (left right: r -> B.box r) (keys: Seq.seq a) (tr: Seq.seq ((a & b) & bool)) (pend: Seq.seq a)
  : Lemma (requires Seq.length tr == 0 /\ Seq.equal pend keys)
          (ensures bf_visited keys tr pend)
  = reveal_opaque (`%bf_visited) (bf_visited #a #b);
    Seq.lemma_eq_elim pend keys

/// The walk of no keys, which made no calls, returned true.
let bf_walked_nil (#a #b: Type0) (keys: Seq.seq a) (tr: Seq.seq ((a & b) & bool))
  : Lemma (requires Seq.length keys == 0 /\ Seq.length tr == 0)
          (ensures bf_walked keys tr true)
          [SMTPat (bf_walked keys tr true)]
  = reveal_opaque (`%bf_walked) (bf_walked #a #b);
    assert (forall (y: a). ~(SF.contains keys y))

/// R27.40. The protocol of `RemoveWhere`'s callback: every call returned true, and `m` is the
/// keys of the calls `f` holds of.
let collected (#a #b: Type0) (tr: Seq.seq ((a & b) & bool)) (m: Seq.seq a) (f: Pulse.Lib.CSharp.Delegate.fn1 a bool) : prop =
  Seq.length m <= Seq.length tr /\
  (forall (i: nat). i < Seq.length tr ==> snd (Seq.index tr i) == true) /\
  (forall (y: a). {:pattern SF.contains m y} SF.contains m y <==> in_trace tr y /\ Pulse.Lib.CSharp.Delegate.apply1 f y == true)

/// A walk that collected is a walk over every key: `m` is the keys `f` holds of.
let collected_walked (#a #b: Type0) (keys: Seq.seq a) (tr: Seq.seq ((a & b) & bool)) (res: bool)
    (m: Seq.seq a) (f: Pulse.Lib.CSharp.Delegate.fn1 a bool)
  : Lemma (requires bf_walked keys tr res /\ collected tr m f)
          (ensures res == true /\
                   (forall (y: a). SF.contains m y <==> SF.contains keys y /\ Pulse.Lib.CSharp.Delegate.apply1 f y == true))
          [SMTPat (bf_walked keys tr res); SMTPat (collected tr m f)]
  = reveal_opaque (`%bf_visited) (bf_visited #a #b);
    reveal_opaque (`%bf_walked) (bf_walked #a #b);
    let aux (y: a) : Lemma (requires in_trace tr y) (ensures SF.contains keys y)
      = let i = FStar.IndefiniteDescription.indefinite_description_ghost nat
                  (fun i -> i < Seq.length tr /\ tkey (Seq.index tr i) == y) in () in
    FStar.Classical.forall_intro (FStar.Classical.move_requires aux)

/// The queue after the walk's dequeue and its enqueues of the front's non-null children.
let bf_next (#r #a #b: Type0) (view: B.box r -> r -> (a & b)) (left right: r -> B.box r)
    (h: heap r) (q: Seq.seq (B.box r) { Seq.length q > 0 /\ mem h (Seq.index q 0) }) : GTot (Seq.seq (B.box r)) =
  let x = Seq.index q 0 in
  let rest = Seq.slice q 1 (Seq.length q) in
  let v = get h x in
  let q1 = if B.is_null (left v) then rest else Seq.snoc rest (left v) in
  if B.is_null (right v) then q1 else Seq.snoc q1 (right v)

/// R27.40. One round of the breadth-first walk: take the front `x` off a walkable queue
/// that owes what the walk has not visited, call the callback on it, and queue its
/// non-null children. A true result keeps the visit at the next queue; a false one ends it.
let bf_dequeue (#r #a #b: Type0) (view: B.box r -> r -> (a & b)) (left right: r -> B.box r)
    (h: heap r) (q: Seq.seq (B.box r)) (keys: Seq.seq a) (tr: Seq.seq ((a & b) & bool))
  : Lemma (requires Seq.length q > 0 /\ walkable view left right h q /\
                    bf_visited keys tr (bpending view left right h q))
          (ensures (let x = Seq.index q 0 in
                    let rest = Seq.slice q 1 (Seq.length q) in
                    mem h x /\ not (B.is_null x) /\
                    (let v = get h x in
                     let kl = Seq.length (okeys false (tree_of view left right h (left v))) in
                     let kr = Seq.length (okeys false (tree_of view left right h (right v))) in
                     Seq.length tr < Seq.length keys /\
                     Seq.length rest + (if B.is_null (left v) then 0 else 1) + (if B.is_null (right v) then 0 else 1)
                       <= Seq.length keys - Seq.length tr - 1 /\
                     Seq.length rest + kl + kr < Seq.length keys - Seq.length tr /\
                     Seq.length rest + 1 + kl + kr <= Seq.length keys - Seq.length tr /\
                     walkable view left right h (bf_next view left right h q) /\
                     bf_visited keys (Seq.snoc tr (view x v, true)) (bpending view left right h (bf_next view left right h q)) /\
                     bf_walked keys (Seq.snoc tr (view x v, false)) false)))
  = reveal_opaque (`%bf_visited) (bf_visited #a #b);
    let x = Seq.index q 0 in
    let rest = Seq.slice q 1 (Seq.length q) in
    bf_front view left right h q;
    let v = get h x in
    let tl = tree_of view left right h (left v) in
    let trr = tree_of view left right h (right v) in
    let l = okeys false tl in
    let rt = okeys false trr in
    let k = fst (view x v) in
    let br = bpending view left right h rest in
    bf_step keys tr l k rt br (view x v, true);
    bf_step keys tr l k rt br (view x v, false);
    if not (B.is_null (left v)) then wf_step view left right h (left v);
    if not (B.is_null (right v)) then wf_step view left right h (right v);
    let q' = bf_next view left right h q in
    let p' = Seq.append (Seq.append br l) rt in
    let lr = Seq.length rest + (if B.is_null (left v) then 0 else 1) + (if B.is_null (right v) then 0 else 1) in
    let q1 = if B.is_null (left v) then rest else Seq.snoc rest (left v) in
    let p1 = Seq.append br l in
    (if B.is_null (left v) then begin
       assert (tl == T.Leaf); Seq.append_empty_r br; assert (bpending view left right h q1 == p1)
     end else bpending_snoc view left right h rest (left v));
    assert (bpending view left right h q1 == p1);
    (if B.is_null (right v) then begin
       assert (trr == T.Leaf); Seq.append_empty_r p1; assert (q' == q1)
     end else begin
       assert (q' == Seq.snoc q1 (right v));
       bpending_snoc view left right h q1 (right v)
     end);
    assert (bpending view left right h q' == p');
    assert (lr <= Seq.length br + Seq.length l + Seq.length rt)
