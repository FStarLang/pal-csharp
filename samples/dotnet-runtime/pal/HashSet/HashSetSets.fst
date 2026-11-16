module HashSetSets

/// Set relations modulo a comparer, for `HashSet<T>`'s set operations (doc/translation.md
/// R30.41). Every definition here is a definition and every lemma is proved; nothing is
/// assumed. In particular the comparer's `Equals` is *not* assumed to be an equivalence
/// (Pulse.Lib.CSharp.Equality leaves it uninterpreted): `equiv c` is a hypothesis that a
/// specification states where it needs it, as `IEqualityComparer<T>`'s documentation states
/// it as an obligation of the comparer.

open FStar.Seq
module Seq = FStar.Seq
module Eq = Pulse.Lib.CSharp.Equality
module HC = Pulse.Lib.CSharp.HashChain
module HSC = HashSetChain

let eq (#t: Type0) (c: option (Eq.comparer t)) (x y: t) : bool = Eq.equals (HSC.eff c) x y

/// `c.Equals` is reflexive, symmetric and transitive.
let equiv (#t: Type0) (c: option (Eq.comparer t)) : prop =
  (forall (x: t). {:pattern eq c x x} eq c x x) /\
  (forall (x y: t). {:pattern eq c x y} eq c x y ==> eq c y x) /\
  (forall (x y z: t). {:pattern eq c x y; eq c y z} eq c x y /\ eq c y z ==> eq c x z)

/// No two elements of `xs` are equal at `c`.
let distinct (#t: Type0) (c: option (Eq.comparer t)) (xs: seq t) : prop =
  forall (i j: nat). {:pattern eq c (Seq.index xs i) (Seq.index xs j)}
    i < Seq.length xs /\ j < Seq.length xs /\ i <> j ==> ~(eq c (Seq.index xs i) (Seq.index xs j))

/// `s` holds, modulo `c`, what `s0` does and `o` does not.
let except (#t: Type0) (c: option (Eq.comparer t)) (s0 o s: seq t) : prop =
  forall (x: t). HSC.mem c s x <==> (HSC.mem c s0 x /\ ~(HSC.mem c o x))

/// Some element of `o` is a member of `s` at `c`.
let overlaps (#t: Type0) (c: option (Eq.comparer t)) (s o: seq t) : prop =
  exists (k: nat). k < Seq.length o /\ HSC.mem c s (Seq.index o k)

let mem_def (#t: Type0) (c: option (Eq.comparer t)) (xs: seq t) (x: t)
  : Lemma (HSC.mem c xs x <==> (exists (p: nat). p < Seq.length xs /\ eq c (Seq.index xs p) x))
  = ()

(* ---------------------------------------------------------------------------------- *)
(* One `Remove` *)

let remove_at_index (#t: Type0) (xs: seq t) (p: nat{p < Seq.length xs}) (q: nat)
  : Lemma (requires q < Seq.length xs - 1)
          (ensures Seq.index (HC.remove_at xs p) q == Seq.index xs (if q < p then q else q + 1))
  = ()

/// What one `Remove(x)` leaves, whether it found `x` or not: exactly the members not equal
/// to `x`, still distinct.
let remove_step (#t: Type0) (c: option (Eq.comparer t)) (xs ys: seq t) (x: t)
  : Lemma (requires equiv c /\ distinct c xs /\
                    (HSC.removed c xs ys x \/ (~(HSC.mem c xs x) /\ ys == xs)))
          (ensures distinct c ys /\
                   (forall (z: t). HSC.mem c ys z <==> (HSC.mem c xs z /\ ~(eq c x z))))
  = if FStar.IndefiniteDescription.strong_excluded_middle (HSC.mem c xs x) then begin
      eliminate exists (p: nat). p < Seq.length xs /\ eq c (Seq.index xs p) x /\ ys == HC.remove_at xs p
      with begin
        let idx (q: nat{q < Seq.length ys}) : nat = if q < p then q else q + 1 in
        let ys_at (q: nat{q < Seq.length ys}) : Lemma (Seq.index ys q == Seq.index xs (idx q)) =
          remove_at_index xs p q in
        let d (i j: nat) : Lemma (i < Seq.length ys /\ j < Seq.length ys /\ i <> j ==>
                                  ~(eq c (Seq.index ys i) (Seq.index ys j))) =
          if i < Seq.length ys && j < Seq.length ys && i <> j then (ys_at i; ys_at j) in
        Classical.forall_intro_2 d;
        let fwd (z: t) : Lemma (HSC.mem c ys z ==> (HSC.mem c xs z /\ ~(eq c x z))) =
          if FStar.IndefiniteDescription.strong_excluded_middle (HSC.mem c ys z) then
            eliminate exists (q: nat). q < Seq.length ys /\ eq c (Seq.index ys q) z
            with begin
              ys_at q;
              let w = Seq.index xs (idx q) in
              assert (eq c w z);
              if eq c x z then begin
                assert (eq c z x); assert (eq c w x); assert (eq c x (Seq.index xs p));
                assert (eq c w (Seq.index xs p))
              end
            end in
        let bwd (z: t) : Lemma ((HSC.mem c xs z /\ ~(eq c x z)) ==> HSC.mem c ys z) =
          if FStar.IndefiniteDescription.strong_excluded_middle (HSC.mem c xs z /\ ~(eq c x z)) then
            eliminate exists (r: nat). r < Seq.length xs /\ eq c (Seq.index xs r) z
            with begin
              if r = p then begin
                assert (eq c x (Seq.index xs p)); assert (eq c x z)
              end else begin
                let q : nat = if r < p then r else r - 1 in
                ys_at q
              end
            end in
        Classical.forall_intro fwd;
        Classical.forall_intro bwd
      end
    end else begin
      let bwd (z: t) : Lemma (HSC.mem c xs z ==> ~(eq c x z)) =
        if FStar.IndefiniteDescription.strong_excluded_middle (HSC.mem c xs z) then
          eliminate exists (r: nat). r < Seq.length xs /\ eq c (Seq.index xs r) z
          with if eq c x z then (assert (eq c z x); assert (eq c (Seq.index xs r) x)) in
      Classical.forall_intro bwd
    end

(* ---------------------------------------------------------------------------------- *)
(* ExceptWith *)

let except_start (#t: Type0) (c: option (Eq.comparer t)) (s: seq t) (o: seq t)
  : Lemma (except c s (Seq.slice o 0 0) s)
  = ()

/// `Remove(o[k])` after removing `o[0..k)`.
let except_step (#t: Type0) (c: option (Eq.comparer t)) (s0 o s s': seq t) (k: nat)
  : Lemma (requires k < Seq.length o /\ equiv c /\ distinct c s /\ except c s0 (Seq.slice o 0 k) s /\
                    (HSC.removed c s s' (Seq.index o k) \/ (~(HSC.mem c s (Seq.index o k)) /\ s' == s)))
          (ensures distinct c s' /\ except c s0 (Seq.slice o 0 (k + 1)) s')
  = let x = Seq.index o k in
    remove_step c s s' x;
    let a = Seq.slice o 0 k in
    let b = Seq.slice o 0 (k + 1) in
    let m (z: t) : Lemma (HSC.mem c b z <==> (HSC.mem c a z \/ eq c x z)) =
      assert (Seq.index b k == x);
      assert (forall (i: nat). i < k ==> Seq.index b i == Seq.index a i) in
    Classical.forall_intro m

let except_done (#t: Type0) (c: option (Eq.comparer t)) (s0 o s: seq t)
  : Lemma (requires except c s0 (Seq.slice o 0 (Seq.length o)) s)
          (ensures except c s0 o s)
  = assert (Seq.equal (Seq.slice o 0 (Seq.length o)) o)

/// Removing everything (`Clear`, or nothing to remove from).
let except_empty (#t: Type0) (c: option (Eq.comparer t)) (s0 o: seq t)
  : Lemma (requires Seq.length s0 == 0) (ensures except c s0 o s0 /\ distinct c s0)
  = ()

(* ---------------------------------------------------------------------------------- *)
(* Overlaps *)

let overlaps_hit (#t: Type0) (c: option (Eq.comparer t)) (s o: seq t) (k: nat)
  : Lemma (requires k < Seq.length o /\ HSC.mem c s (Seq.index o k)) (ensures overlaps c s o)
  = ()

let no_overlap (#t: Type0) (c: option (Eq.comparer t)) (s o: seq t) (k: int) : prop =
  0 <= k /\ k <= Seq.length o /\ (forall (j: nat). j < k ==> ~(HSC.mem c s (Seq.index o j)))

let no_overlap_done (#t: Type0) (c: option (Eq.comparer t)) (s o: seq t)
  : Lemma (requires no_overlap c s o (Seq.length o)) (ensures ~(overlaps c s o))
  = ()

(* ---------------------------------------------------------------------------------- *)
(* Pigeonhole *)

/// The first position of `xs` at or after `i` equal to `y` at `c`, if any.
let rec find_from (#t: Type0) (c: option (Eq.comparer t)) (xs: seq t) (y: t) (i: nat)
  : Tot (r: option nat{match r with
                       | Some p -> i <= p /\ p < Seq.length xs /\ eq c y (Seq.index xs p)
                       | None -> forall (j: nat). i <= j /\ j < Seq.length xs ==> ~(eq c y (Seq.index xs j))})
        (decreases Seq.length xs - i)
  = if i >= Seq.length xs then None
    else if eq c y (Seq.index xs i) then Some i
    else find_from c xs y (i + 1)

/// Distinct elements, each a member of `ys`, are no more than `ys`'s length: an injection
/// into `ys`'s positions. It needs `equiv`: two elements equal to one `y` are equal.
let rec pigeonhole (#t: Type0) (c: option (Eq.comparer t)) (xs ys: seq t)
  : Lemma (requires equiv c /\ distinct c xs /\ HSC.all_in c ys xs)
          (ensures Seq.length xs <= Seq.length ys)
          (decreases Seq.length ys)
  = if Seq.length ys = 0 then begin
      if Seq.length xs > 0 then assert (HSC.mem c ys (Seq.index xs 0))
    end else begin
      let n = Seq.length ys - 1 in
      let y = Seq.index ys n in
      let ys' = Seq.slice ys 0 n in
      let in_prefix (x: t) : Lemma (requires HSC.mem c ys x /\ ~(eq c y x)) (ensures HSC.mem c ys' x) =
        eliminate exists (q: nat). q < Seq.length ys /\ eq c (Seq.index ys q) x
        with (assert (q <> n); assert (Seq.index ys' q == Seq.index ys q)) in
      match find_from c xs y 0 with
      | None ->
        let a (i: nat) : Lemma (i < Seq.length xs ==> HSC.mem c ys' (Seq.index xs i)) =
          if i < Seq.length xs then begin
            assert (HSC.mem c ys (Seq.index xs i));
            in_prefix (Seq.index xs i)
          end in
        Classical.forall_intro a;
        pigeonhole c xs ys'
      | Some p ->
        let xs' = HC.remove_at xs p in
        let at (q: nat{q < Seq.length xs'}) : Lemma (Seq.index xs' q == Seq.index xs (if q < p then q else q + 1)) =
          remove_at_index xs p q in
        let d (i j: nat) : Lemma (i < Seq.length xs' /\ j < Seq.length xs' /\ i <> j ==>
                                  ~(eq c (Seq.index xs' i) (Seq.index xs' j))) =
          if i < Seq.length xs' && j < Seq.length xs' && i <> j then (at i; at j) in
        Classical.forall_intro_2 d;
        let a (i: nat) : Lemma (i < Seq.length xs' ==> HSC.mem c ys' (Seq.index xs' i)) =
          if i < Seq.length xs' then begin
            at i;
            let r = if i < p then i else i + 1 in
            let x = Seq.index xs r in
            assert (HSC.mem c ys x);
            if eq c y x then begin
              assert (eq c x y); assert (eq c x (Seq.index xs p))
            end;
            in_prefix x
          end in
        Classical.forall_intro a;
        pigeonhole c xs' ys'
    end

(* ---------------------------------------------------------------------------------- *)
(* The forms the C# wrappers call: an implication, so that a contract states `equiv` and
   `distinct` as hypotheses of its conclusion rather than as preconditions. *)

let except_step_imp (#t: Type0) (c: option (Eq.comparer t)) (s0 o s s': seq t) (k: nat{k < Seq.length o})
  : Lemma (ensures (let o0 = Seq.slice o 0 k in let o1 = Seq.slice o 0 (k + 1) in
                    (equiv c /\ distinct c s /\ except c s0 o0 s /\
                    (HSC.removed c s s' (Seq.index o k) \/ (~(HSC.mem c s (Seq.index o k)) /\ s' == s))) ==>
                   (distinct c s' /\ except c s0 o1 s')))
  = Classical.move_requires (fun (_: unit) -> except_step c s0 o s s' k) ()

let except_done_imp (#t: Type0) (c: option (Eq.comparer t)) (s0 o s: seq t)
  : Lemma (except c s0 (Seq.slice o 0 (Seq.length o)) s ==> except c s0 o s)
  = Classical.move_requires (except_done c s0 o) s

let no_overlap_step (#t: Type0) (c: option (Eq.comparer t)) (s o: seq t) (k: int)
  : Lemma (requires 0 <= k /\ k < Seq.length o /\ no_overlap c s o k /\ ~(HSC.mem c s (Seq.index o k)))
          (ensures no_overlap c s o (k + 1))
  = ()

(* ---------------------------------------------------------------------------------- *)
(* Overlaps along a walk of a set's prefixes (R30.35) *)

/// No element of `xs` is a member of `s`.
let none_in (#t: Type0) (c: option (Eq.comparer t)) (s xs: seq t) : prop =
  forall (i: nat). i < Seq.length xs ==> ~(HSC.mem c s (Seq.index xs i))

let none_in_snoc (#t: Type0) (c: option (Eq.comparer t)) (s xs: seq t) (x: t)
  : Lemma (none_in c s (Seq.snoc xs x) <==> (none_in c s xs /\ ~(HSC.mem c s x)))
          [SMTPat (none_in c s (Seq.snoc xs x))]
  = let ys = Seq.snoc xs x in
    assert (forall (i: nat). i < Seq.length xs ==> Seq.index ys i == Seq.index xs i);
    assert (Seq.index ys (Seq.length xs) == x)

let none_in_empty (#t: Type0) (c: option (Eq.comparer t)) (s xs: seq t)
  : Lemma (requires Seq.length xs == 0) (ensures none_in c s xs)
  = ()

/// A member found at the end of a prefix of the walk is an overlap of the whole.
let overlaps_walk (#t: Type0) (c: option (Eq.comparer t)) (s: seq t) (ps: seq (seq t)) (xs: seq t) (i: int)
  : Lemma (requires HSC.walk ps xs /\ 0 <= i /\ i < Seq.length ps /\ Seq.length (Seq.index ps i) > 0 /\
                    HSC.mem c s (Seq.index (Seq.index ps i) (Seq.length (Seq.index ps i) - 1)))
          (ensures overlaps c s xs)
  = let a = Seq.index ps i in
    assert (Seq.index a (Seq.length a - 1) == Seq.index xs (Seq.length a - 1))

/// None of the whole walk is a member: no overlap.
let none_in_walk (#t: Type0) (c: option (Eq.comparer t)) (s: seq t) (ps: seq (seq t)) (xs: seq t)
  : Lemma (requires HSC.walk ps xs /\ none_in c s (Seq.index ps (Seq.length ps - 1)))
          (ensures ~(overlaps c s xs))
  = ()

(* ---------------------------------------------------------------------------------- *)
(* RemoveWhere *)

/// Every element of `s` is a member of `s`, at an equivalence.
let all_in_refl (#t: Type0) (c: option (Eq.comparer t)) (s: seq t)
  : Lemma (requires equiv c) (ensures HSC.all_in c s s)
  = let f (i: nat) : Lemma (i < Seq.length s ==> HSC.mem c s (Seq.index s i)) =
      if i < Seq.length s then begin
        assert (eq c (Seq.index s i) (Seq.index s i));
        mem_def c s (Seq.index s i)
      end in
    Classical.forall_intro f

let all_in_refl_imp (#t: Type0) (c: option (Eq.comparer t)) (s: seq t)
  : Lemma (equiv c ==> HSC.all_in c s s)
  = Classical.move_requires (all_in_refl c) s

/// One `Remove` keeps the elements distinct, and each of them one of `s0`'s.
let remove_where_step (#t: Type0) (c: option (Eq.comparer t)) (s0 xs ys: seq t) (x: t)
  : Lemma (requires equiv c /\ distinct c xs /\ HSC.all_in c s0 xs /\ (HSC.removed c xs ys x \/ ys == xs))
          (ensures distinct c ys /\ HSC.all_in c s0 ys)
  = if FStar.IndefiniteDescription.strong_excluded_middle (ys == xs) then ()
    else begin
      remove_step c xs ys x;
      eliminate exists (p: nat). p < Seq.length xs /\ eq c (Seq.index xs p) x /\ ys == HC.remove_at xs p
      with begin
        let f (q: nat) : Lemma (q < Seq.length ys ==> HSC.mem c s0 (Seq.index ys q)) =
          if q < Seq.length ys then remove_at_index xs p q in
        Classical.forall_intro f
      end
    end

let remove_where_step_imp (#t: Type0) (c: option (Eq.comparer t)) (s0 xs ys: seq t) (x: t)
  : Lemma ((equiv c /\ distinct c xs /\ HSC.all_in c s0 xs /\ (HSC.removed c xs ys x \/ ys == xs)) ==>
           (distinct c ys /\ HSC.all_in c s0 ys))
  = Classical.move_requires (fun (_: unit) -> remove_where_step c s0 xs ys x) ()
