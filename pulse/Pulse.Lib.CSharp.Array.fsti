module Pulse.Lib.CSharp.Array
#lang-pulse

/// The C# array type, `T[]`.
///
/// A CLR array is a *fully initialized* object that carries its own length in
/// its object header. That is simpler than a C array in two ways, and pal-csharp
/// exploits both:
///
///   * There is no partially-initialized state, so the mask/`MaybeUninit`
///     machinery `Pulse.Lib.C.Array` needs has no analogue here. The resource
///     for `T[] a` is just `Pulse.Lib.Array.pts_to a #p (s: Seq.seq t)`.
///   * The length is a runtime value, obtained with `length_i32`, whereas
///     `Pulse.Lib.Array.Core.length` is ghost.
///
/// The one thing that is *harder* than C is indexing: `System.Array.Length` and
/// every C# subscript are signed `int`, while Pulse arrays are `size_t`-indexed.
/// The translation scheme (doc/translation.md, R3.3) crosses that boundary in
/// exactly one place, `Pulse.Lib.CSharp.Casts.idx`, and this module supplies the
/// `int`-indexed read and write built on it.

include Pulse.Lib.Array

open Pulse
open Pulse.Lib.CSharp.Assumptions
open Pulse.Lib.CSharp.Casts
open Pulse.Lib.CSharp.Inhabited
open Pulse.Lib.SmallType

module A = Pulse.Lib.Array
module I32 = FStar.Int32
module SZ = FStar.SizeT
module Seq = FStar.Seq

/// The pure model of the CLR array-length header field.
///
/// MODELING AXIOM, in two parts. A CLR array's length is fixed at allocation and
/// stored in the object header, so `a.Length` is a *pure* function of `a` --
/// unlike `Pulse.Lib.Array.length`, which is ghost, and unlike a C array, which
/// has no length at all. And because `System.Array.Length` has type `int`, no
/// CLR array holds more than `Int32.MaxValue` elements; `arr_length_v` is what
/// makes that bound available to every index obligation.
val arr_length (#t: Type0) (a: array t) : I32.t

val arr_length_v (#t: Type0) (a: array t)
  : Lemma (I32.v (arr_length a) == A.length a)
          [SMTPat (I32.v (arr_length a))]

/// `System.Array.Length`.
///
/// The `rewrites_to` is load-bearing rather than cosmetic: without it the value
/// returned here is an opaque existential, and a loop guard that mentions
/// `a.Length` -- which is every counted `for` over an array -- cannot be given
/// a postcondition. With it, `length_i32 a` is definitionally `arr_length a`,
/// and the guard is an ordinary pure comparison.
fn length_i32 (#t: Type0) (a: array t) (#p: perm) (#s: Ghost.erased (Seq.seq t))
  preserves A.pts_to a #p s
  returns  n : I32.t
  ensures  rewrites_to n (arr_length a)
  ensures  pure (I32.v n == Seq.length s)

/// `a[i]`, at a C# `int` index.
///
/// The caller owes `0 <= i` and `i < a.Length`; the emitter generates both as
/// proof obligations at every subscript (doc/translation.md, R6.4).
fn read (#t: Type0) (a: array t) (i: I32.t)
        (#p: perm)
        (#s: Ghost.erased (Seq.seq t) { I32.v i >= 0 /\ I32.v i < Seq.length s })
  preserves A.pts_to a #p s
  returns  x : t
  ensures  rewrites_to x (Seq.index s (I32.v i))

/// `a[i] = x`, at a C# `int` index.
fn write (#t: Type0) (a: array t) (i: I32.t) (x: t)
         (#s: Ghost.erased (Seq.seq t) { I32.v i >= 0 /\ I32.v i < Seq.length s })
  requires A.pts_to a s
  ensures  A.pts_to a (Seq.upd s (I32.v i) x)

/// `new T[n]`, which the CLR zero-fills with `default(T)`.
///
/// MODELING AXIOM. `Pulse.Lib.Array.alloc` is documented as unsound (it has no
/// companion `free` obligation, and C stack arrays do not outlive their frame);
/// for the CLR, where allocation is garbage collected and always succeeds, an
/// allocation with no deallocation obligation is exactly right.
fn alloc (#t: Type0) (n: I32.t { I32.v n >= 0 }) (init: t)
  requires emp
  returns  a : array t
  ensures  A.pts_to a (Seq.create (I32.v n) init)
