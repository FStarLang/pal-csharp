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
  forall (i: nat). i < Seq.length s ==> wf left right h (Seq.index s i) /\ not (B.is_null (Seq.index s i))

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
