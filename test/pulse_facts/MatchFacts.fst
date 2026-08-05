module MatchFacts
#lang-pulse

(* §0 probe for R5.14: should a C# `switch` become a Pulse `match`?

   R5.14 desugars `switch` to an if/else chain. When it was written that was not a
   choice — Pulse could not scrutinise a machine integer at all, and a chain was the
   only target. FStarLang/FStar#4374 ("Preserve machine integer match patterns", merged
   2026-08-02) changed that, so the question is now a real one and this file settles it
   with the checker rather than with an opinion.

   Everything below verifies. The one thing that does *not* is recorded at the end, and
   it is the one that decides the design. *)

open Pulse
module I32 = FStar.Int32
module U8 = FStar.UInt8

(* ------------------------------------------------------------------------- *)
(* 1. Pulse has a stateful `match`.                                           *)
(* ------------------------------------------------------------------------- *)

fn match_bool (b: bool)
requires emp
returns r:I32.t
ensures pure (I32.v r == (if b then 1 else 0))
{
  match b { true -> { 1l } false -> { 0l } }
}

(* ------------------------------------------------------------------------- *)
(* 2. Since #4374 it scrutinises a machine integer, which is what a C# switch  *)
(*    does. Before that PR this file's `0l` was read as a `Prims.int` pattern  *)
(*    and rejected:                                                           *)
(*                                                                            *)
(*      Type of pattern (Prims.int) does not match type of scrutinee          *)
(*      (FStar.Int32.t)                                                       *)
(* ------------------------------------------------------------------------- *)

fn match_i32 (k: I32.t)
requires emp
returns r:I32.t
ensures emp
{
  match k { 0l -> { 10l } 2l -> { 20l } _ -> { 1l } }
}

fn match_u8 (b: U8.t)
requires emp
returns r:bool
ensures emp
{
  match b { 0uy -> { true } _ -> { false } }
}

(* ------------------------------------------------------------------------- *)
(* 3. An arm gives exactly the equality the corresponding `if` branch gives.   *)
(*    This is why `match` would buy no proof strength over a chain: the arm's  *)
(*    hypothesis is `I32.v k == 0`, which is what `if (I32.eq k 0l)` already   *)
(*    puts in the context. A machine integer is not an inductive type, so      *)
(*    there is no case split to be had — only the equality.                    *)
(* ------------------------------------------------------------------------- *)

fn match_gives_equality (k: I32.t)
requires emp
returns r:I32.t
ensures emp
{
  match k {
    0l -> { assert (pure (I32.v k == 0)); 10l }
    _  -> { 1l }
  }
}

fn chain_gives_equality (k: I32.t)
requires emp
returns r:I32.t
ensures emp
{
  if (I32.eq k 0l) { assert (pure (I32.v k == 0)); 10l } else { 1l }
}

(* ------------------------------------------------------------------------- *)
(* 4. THE DECIDING FACT, and the reason R5.14 keeps the chain.                 *)
(*                                                                            *)
(*    Pulse has no or-patterns. This does not parse:                           *)
(*                                                                            *)
(*      match k { 0l | 1l -> { 10l }   _ -> { 1l } }                          *)
(*      ^ Error 168: Syntax error                                             *)
(*                                                                            *)
(*    (Checked on nightly-2026-08-05, i.e. after #4374, and on the pure F*     *)
(*    side `let f n = match n with | 0 | 1 -> 10 | _ -> 1` *does* verify — so  *)
(*    this is a property of Pulse's match, not of F*'s.)                       *)
(*                                                                            *)
(*    A C# section carries a *set* of labels:                                  *)
(*                                                                            *)
(*      case 0:                                                                *)
(*      case 1:                                                                *)
(*          S;                                                                 *)
(*          break;                                                             *)
(*                                                                            *)
(*    is one section with two labels, not two sections. With no or-pattern,    *)
(*    `match` can only express it by duplicating S once per label — and the    *)
(*    duplication is unbounded, since a section may carry any number of        *)
(*    labels. S is the user's code: their asserts, their lemma calls, their    *)
(*    loops. Duplicating it duplicates the proof obligations they wrote once.  *)
(*                                                                            *)
(*    A disjunction costs nothing and has no such limit, which is the whole    *)
(*    argument:                                                                *)
(* ------------------------------------------------------------------------- *)

fn stacked_labels_as_a_chain (k: I32.t)
requires emp
returns r:I32.t
ensures emp
{
  if (I32.eq k 0l || I32.eq k 1l) { 10l } else { 1l }
}
