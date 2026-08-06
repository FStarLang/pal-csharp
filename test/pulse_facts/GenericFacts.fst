module GenericFacts
#lang-pulse

(* §0 probe for generics (M8): what does a C# type parameter cost in Pulse?

   The question this file settles is not "does F* have polymorphism" -- it plainly does --
   but the one that decides the size of the milestone: whether `Pulse.Lib.CSharp.*`, which
   every translated program is built on, works at an *abstract* element type, or only at
   the handful of concrete types the suite has used so far. If the library needed a
   parallel polymorphic copy, generics would be a library milestone as well as a frontend
   one.

   It does not. Everything below verifies against the pinned toolchain with no change to
   `Pulse.Lib.CSharp.Array`, whose operations are already `#t: Type0`.

   These are F62-F64 of doc/translation.md §1. Like the other files here they are NOT
   translation targets and NOT golden files: nothing in the emitter produces these shapes
   yet, and §0 requires the facts to be probed and pinned before a rule is written. *)

open Pulse
open FStar.Ghost

module CA = Pulse.Lib.CSharp.Array
module A = Pulse.Lib.Array
module I32 = FStar.Int32
module Seq = FStar.Seq

(* ------------------------------------------------------------------------- *)
(* F62. The C# array library applies at an abstract element type.             *)
(*                                                                            *)
(* `CA.read` and `CA.write` are declared `(#t: Type0)`, so a Pulse fn that is  *)
(* itself polymorphic can call them with the type variable it was given. This *)
(* is what every generic method over `T[]` reduces to, and it is the fact that *)
(* keeps generics out of the support library.                                 *)
(* ------------------------------------------------------------------------- *)

fn generic_get (#t: Type0) (a: A.array t) (i: I32.t) (#s: erased (Seq.seq t))
  requires A.pts_to a s ** pure (I32.v i >= 0 /\ I32.v i < Seq.length s)
  returns  x: t
  ensures  A.pts_to a s **
           pure (I32.v i >= 0 /\ I32.v i < Seq.length s /\
                 x == Seq.index s (I32.v i))
{
  CA.read a i
}

fn generic_set (#t: Type0) (a: A.array t) (i: I32.t) (v: t) (#s: erased (Seq.seq t))
  requires A.pts_to a s ** pure (I32.v i >= 0 /\ I32.v i < Seq.length s)
  ensures  exists* s'. A.pts_to a s' **
           pure (I32.v i >= 0 /\ I32.v i < Seq.length s /\
                 s' == Seq.upd s (I32.v i) v)
{
  CA.write a i v
}

(* ------------------------------------------------------------------------- *)
(* F63. A generic struct is an ordinary parameterised record.                  *)
(*                                                                            *)
(* This is the `ArraySegment<T>` / `Span<T>` shape: a record holding an array  *)
(* of the parameter type together with an offset and a count. The pure         *)
(* well-formedness predicate over it is parameterised the same way, so R3.x's  *)
(* treatment of a struct needs no new idea -- only a binder.                   *)
(*                                                                            *)
(* `examples/adler32` had to spell `ArraySegment<byte>` out as three separate  *)
(* parameters. This is the fact that says it will not have to.                 *)
(* ------------------------------------------------------------------------- *)

noeq type segment (t: Type0) = { arr: A.array t; off: I32.t; cnt: I32.t }

let seg_ok (#t: Type0) (g: segment t) (s: Seq.seq t) : prop =
  I32.v g.off >= 0 /\ I32.v g.cnt >= 0 /\ I32.v g.off + I32.v g.cnt <= Seq.length s

fn seg_first (#t: Type0) (g: segment t) (#s: erased (Seq.seq t))
  requires A.pts_to g.arr s ** pure (seg_ok g s /\ I32.v g.cnt > 0)
  returns  x: t
  ensures  A.pts_to g.arr s
{
  CA.read g.arr g.off
}

(* ------------------------------------------------------------------------- *)
(* F64. Instantiation composes: a generic fn may call a generic fn at its own  *)
(* type variable.                                                             *)
(*                                                                            *)
(* So a generic method calling another generic method needs no monomorphising  *)
(* pass in the emitter -- the type argument is inferred at the call, exactly   *)
(* as a concrete one is today. Without this fact the milestone would have to   *)
(* choose between specialising every instantiation (and losing the one-module- *)
(* per-method structure R2.x depends on) and emitting explicit type arguments  *)
(* everywhere.                                                                *)
(* ------------------------------------------------------------------------- *)

fn generic_swap (#t: Type0) (a: A.array t) (i j: I32.t) (#s: erased (Seq.seq t))
  requires A.pts_to a s ** pure (I32.v i >= 0 /\ I32.v i < Seq.length s /\
                                 I32.v j >= 0 /\ I32.v j < Seq.length s)
  ensures  exists* s'. A.pts_to a s' ** pure (Seq.length s' == Seq.length s)
{
  let x = generic_get a i;
  let y = generic_get a j;
  generic_set a i y;
  generic_set a j x;
}
