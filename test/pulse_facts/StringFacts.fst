module StringFacts
#lang-pulse

(* §0 probe for strings: what would a C# `string` have to be?

   This file is the road *not* taken in M8 -- generics went first -- and it exists so that
   the decision rests on a measured cost rather than on an impression, and so that nobody
   probes it a second time.

   The finding is that a C# string is unusually cheap to model, for one reason: it is
   immutable. An array needs `pts_to` because two references to it can disagree about what
   it holds; a string cannot change, so there is nothing to own and no permission to
   thread. It is a *pure value*, and every operation on it is a pure function.

   This is F65 of doc/translation.md §1. What it does not measure is the surface area --
   `Substring`, `IndexOf`, `Split`, concatenation and formatting are each a library
   obligation, and that, not the encoding, is what makes strings a milestone rather than
   an afternoon. *)

open Pulse
module Seq = FStar.Seq
module S = FStar.String

(* ------------------------------------------------------------------------- *)
(* 1. A string is a pure value in a specification.                            *)
(* ------------------------------------------------------------------------- *)

let str_len_is_pure (s: string) : nat = S.strlen s

(* C# `==` on strings is value equality, and so is F*'s. *)
let str_eq (a b: string) : bool = a = b

(* ------------------------------------------------------------------------- *)
(* 2. The model an indexing specification would need.                          *)
(* ------------------------------------------------------------------------- *)

let str_model (s: string) : Seq.seq FStar.Char.char =
  Seq.seq_of_list (S.list_of_string s)

let str_model_len (s: string)
  : Lemma (Seq.length (str_model s) == S.strlen s)
  = S.list_of_string_of_list (S.list_of_string s)

(* ------------------------------------------------------------------------- *)
(* 3. A Pulse fn takes and returns a string with no separation logic at all.  *)
(*                                                                            *)
(* Note `requires emp`: this is the whole point. A string parameter costs a   *)
(* translated method nothing, where an array parameter costs it a `pts_to`    *)
(* in both the precondition and the postcondition.                            *)
(* ------------------------------------------------------------------------- *)

fn str_length (s: string)
  requires emp
  returns  n: nat
  ensures  pure (n == S.strlen s)
{
  S.strlen s
}

fn str_pick (a b: string) (flag: bool)
  requires emp
  returns  r: string
  ensures  pure (r == (if flag then a else b))
{
  if flag { a } else { b }
}
