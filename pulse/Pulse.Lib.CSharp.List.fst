module Pulse.Lib.CSharp.List

/// The list vocabulary a C# specification may use beyond what `FStar.List.Tot`
/// already provides (doc/translation.md R15.7).
///
/// Everything here is *total* and *unrefined*. That is the whole design rule of this
/// module, and it is not a stylistic preference: a C# index is an `int`, so the term a
/// specification emits for `l.Take(i)` is `take l (I32.v var_i)` with nothing constraining
/// `I32.v var_i` at the point the term is *typed*. A refined argument (`n: nat{n <= length
/// l}`) would make that term ill-typed until a side condition is discharged, and the side
/// condition is not available where R3.9b puts the conjunct. Clamping instead — a negative
/// count takes nothing, an over-long count takes everything — keeps every emitted term
/// well typed by construction, and the bounds the user actually cares about are stated in
/// their own `[Requires]`, where they belong.
///
/// The lemmas are the ones a *client* needs and are stated with SMT patterns, so that a
/// C# method whose postcondition is `Result.Elements == x.Elements.Take(i)` gets the
/// length and index facts about `take` without naming them.

module L = FStar.List.Tot

(* ------------------------------------------------------------------------ *)
(* take / drop                                                              *)
(* ------------------------------------------------------------------------ *)

/// The first `n` elements, clamped at both ends.
let rec take (#a: Type) (l: list a) (n: int) : Tot (list a) (decreases l) =
  if n <= 0 then []
  else match l with
       | [] -> []
       | hd :: tl -> hd :: take tl (n - 1)

/// Everything but the first `n` elements, clamped at both ends.
let rec drop (#a: Type) (l: list a) (n: int) : Tot (list a) (decreases l) =
  if n <= 0 then l
  else match l with
       | [] -> []
       | _ :: tl -> drop tl (n - 1)

let rec take_length (#a: Type) (l: list a) (n: int)
  : Lemma (ensures L.length (take l n) == (if n <= 0 then 0
                                           else if n >= L.length l then L.length l
                                           else n))
          (decreases l)
          [SMTPat (L.length (take l n))]
  = if n <= 0 then () else match l with [] -> () | _ :: tl -> take_length tl (n - 1)

let rec drop_length (#a: Type) (l: list a) (n: int)
  : Lemma (ensures L.length (drop l n) == (if n <= 0 then L.length l
                                           else if n >= L.length l then 0
                                           else L.length l - n))
          (decreases l)
          [SMTPat (L.length (drop l n))]
  = if n <= 0 then () else match l with [] -> () | _ :: tl -> drop_length tl (n - 1)

let rec take_drop (#a: Type) (l: list a) (n: int)
  : Lemma (ensures L.append (take l n) (drop l n) == l) (decreases l)
          [SMTPat (L.append (take l n) (drop l n))]
  = if n <= 0 then () else match l with [] -> () | _ :: tl -> take_drop tl (n - 1)

(* ------------------------------------------------------------------------ *)
(* insert / remove at an index                                              *)
(* ------------------------------------------------------------------------ *)

/// `l` with `x` spliced in so that it becomes element `i`. An index past the end
/// appends; a negative index prepends.
let rec insert_at (#a: Type) (l: list a) (i: int) (x: a) : Tot (list a) (decreases l) =
  if i <= 0 then x :: l
  else match l with
       | [] -> [x]
       | hd :: tl -> hd :: insert_at tl (i - 1) x

/// `l` without element `i`. An out-of-range index — negative, or past the end — removes
/// nothing, which is what makes the length lemma below a single equation.
let rec remove_at (#a: Type) (l: list a) (i: int) : Tot (list a) (decreases l) =
  if i < 0 then l
  else match l with
       | [] -> []
       | hd :: tl -> if i = 0 then tl else hd :: remove_at tl (i - 1)

let rec insert_at_length (#a: Type) (l: list a) (i: int) (x: a)
  : Lemma (ensures L.length (insert_at l i x) == L.length l + 1) (decreases l)
          [SMTPat (L.length (insert_at l i x))]
  = if i <= 0 then () else match l with [] -> () | _ :: tl -> insert_at_length tl (i - 1) x

let rec remove_at_length (#a: Type) (l: list a) (i: int)
  : Lemma (ensures L.length (remove_at l i) ==
                     (if 0 <= i && i < L.length l then L.length l - 1 else L.length l))
          (decreases l)
          [SMTPat (L.length (remove_at l i))]
  = if i < 0 then ()
    else match l with [] -> () | _ :: tl -> if i = 0 then () else remove_at_length tl (i - 1)

(* ------------------------------------------------------------------------ *)
(* reverse                                                                  *)
(* ------------------------------------------------------------------------ *)

/// `FStar.List.Tot.rev` under this module's name, so that a specification names one
/// module for all of its list vocabulary.
let rev (#a: Type) (l: list a) : list a = L.rev l

let rev_length (#a: Type) (l: list a)
  : Lemma (ensures L.length (rev l) == L.length l) [SMTPat (L.length (rev l))]
  = L.rev_length l

/// The equation an in-place reversal loop proves its invariant with: reversing a cons is
/// reversing the tail and appending the head. `FStar.List.Tot.rev` is defined by an
/// accumulator, so this is not definitional and is exactly the step that is needed.
let rev_cons (#a: Type) (hd: a) (tl: list a)
  : Lemma (ensures rev (hd :: tl) == L.append (rev tl) [hd])
          [SMTPat (rev (hd :: tl))]
  = L.rev_rev' (hd :: tl); L.rev_rev' tl

/// Associativity, which an accumulating reversal needs to move a `[hd]` out of the way.
let rec append_assoc (#a: Type) (l1 l2 l3: list a)
  : Lemma (ensures L.append (L.append l1 l2) l3 == L.append l1 (L.append l2 l3))
          (decreases l1)
          [SMTPat (L.append (L.append l1 l2) l3)]
  = match l1 with [] -> () | _ :: tl -> append_assoc tl l2 l3
