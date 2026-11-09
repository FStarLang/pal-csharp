module Func_InsertionSort
#lang-pulse

/// DERIVED, NOT AUTHORED — a library-adequacy probe (plan §7.2).
///
/// Every line below was produced by hand-executing doc/translation.md on the
/// C# in `InsertionSort.cs` in this directory. It is deliberately verbose and
/// machine-shaped: locals are `ref` cells even when never reassigned (R5.2),
/// every read is a `!` (R6.1), every effectful subexpression is let-bound in
/// C#'s left-to-right order (R6.2), the short-circuiting guard is the ordinary
/// compositional expansion (R6.3), and both loops are loops (§0 rule 2). An F*
/// programmer would write none of this; that is the point.
///
/// What the probe is *for*: to find out, before any emitter code exists,
/// whether `Pulse.Lib.CSharp.*` is strong enough that the mechanical output is
/// provable from the user's annotations alone. Where it is not, the fix is in
/// the library or in the annotation surface — never in the emitter (§0 rule 3).

open Pulse
open Pulse.Lib.CSharp.Array
open Pulse.Lib.CSharp.Casts
open Let_Sorted

module R = Pulse.Lib.Reference
module A = Pulse.Lib.CSharp.Array
module I32 = FStar.Int32
module Seq = FStar.Seq
module CS = Pulse.Lib.CSharp.Seq

fn func_InsertionSort (var_a: array I32.t) (#s0: erased (Seq.seq I32.t))
  requires A.pts_to var_a s0
  ensures  exists* s'. A.pts_to var_a s' **
           pure (Seq.length s' == Seq.length s0 /\
                 CS.is_permutation s' (reveal s0))
{
  // R5.7 (Normalize): `for (int i = 1; i < a.Length; i++)` became
  //   `{ int i = 1; while (i < a.Length) { <body>; i = i + 1; } }`.
  // R5.2: `int i = 1;`
  let mut var_i = 1l;

  // R5.6 + R6.2 + R3.3: the guard `i < a.Length` A-normalises to a stateful
  // block, which F1 permits directly.
  while (
    let t0 = !var_i;
    let t1 = length_i32 var_a;
    I32.lt t0 t1
  )
  // R5.8 (live inference): `var_i` and `var_a` are the locals the loop's body,
  // guard and invariants mention, so they contribute the resource conjuncts.
  // The pure conjuncts are the user's `Pal.Invariant`s, in source order.
  invariant exists* vi s.
    R.pts_to var_i vi ** A.pts_to var_a s **
    pure (Seq.length s == Seq.length s0 /\
          1 <= I32.v vi /\
          CS.is_permutation s (reveal s0))
  // R5.9 case 2: an increasing `int` counter is bounded by the type, so the
  // measure needs no reference to the loop's upper bound — which is important
  // here, because that bound (`a.Length`) is not a pure expression.
  decreases (pow2 31 - I32.v !var_i)
  {
    // R5.8b (frame for unassigned locals): the inner loop never assigns `i`,
    // so its value is *fixed* across that loop rather than existentially
    // quantified by it. Naming it here is what lets the inner invariant say so.
    with vi_1. assert (R.pts_to var_i vi_1);

    // R5.2 + R6.2 + R6.5: `int key = a[i];`
    let t2 = !var_i;
    let t3 = read var_a t2;
    let mut var_key = t3;

    // R5.2 + R6.4: `int j = i - 1;`
    let t4 = !var_i;
    let t5 = I32.sub t4 1l;
    let mut var_j = t5;

    // R5.6 + R6.3: `while (j >= 0 && a[j] > key)`. The short-circuit expansion
    // is the same rule used for any `&&`; nothing about it is loop-specific.
    while (
      let t6 = !var_j;
      let t7 = I32.gte t6 0l;
      if (t7) {
        let t8 = !var_j;
        let t9 = read var_a t8;
        let t10 = !var_key;
        I32.gt t9 t10
      } else {
        false
      }
    )
    invariant exists* vj vkey s.
      R.pts_to var_j vj ** R.pts_to var_key vkey ** R.pts_to var_i vi_1 **
      A.pts_to var_a s **
      pure (Seq.length s == Seq.length s0 /\
            (-1) <= I32.v vj /\ I32.v vj < I32.v vi_1 /\
            I32.v vi_1 < Seq.length s /\ 1 <= I32.v vi_1 /\
            CS.is_permutation (Seq.upd s (I32.v vj + 1) vkey) (reveal s0))
    // R5.9 case 1: the user's `Pal.Decreases(j + 1)`.
    decreases (I32.v !var_j + 1)
    {
      // R5.11: the user's `[Lemma]` call
      //   `PalSeq.UpdShiftIsPermutation(a, j, key);`
      // discharges the permutation step. The emitter contributes nothing here.
      with vj vkey s. assert (R.pts_to var_j vj ** R.pts_to var_key vkey **
                              A.pts_to var_a s);
      CS.upd_shift_is_permutation s (I32.v vj) vkey;

      // R5.3 + R6.2: `a[j + 1] = a[j];` — C# evaluates the target's index
      // before the right-hand side, so the lifted bindings appear in that order.
      let t11 = !var_j;
      let t12 = I32.add t11 1l;
      let t13 = !var_j;
      let t14 = read var_a t13;
      write var_a t12 t14;

      // R5.3 (Normalize turned `j--` into `j = j - 1`).
      let t15 = !var_j;
      let t16 = I32.sub t15 1l;
      var_j := t16;
    };

    // R5.3 + R6.2: `a[j + 1] = key;`
    let t17 = !var_j;
    let t18 = I32.add t17 1l;
    let t19 = !var_key;
    write var_a t18 t19;

    // R5.7: the `for` step `i = i + 1;`
    let t20 = !var_i;
    let t21 = I32.add t20 1l;
    var_i := t21;
  };
  ()
}
