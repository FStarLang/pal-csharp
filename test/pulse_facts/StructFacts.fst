module StructFacts

/// Regression tests for the struct facts doc/translation.md R3.4-R3.6 depend on.
///
/// Like PulseFacts, these are NOT translation targets and NOT golden files. They pin
/// toolchain behaviour so that F10, F11 and F12 cannot silently regress under an F*
/// version bump. The shapes here are exactly the ones the emitter produces.

module I32 = FStar.Int32
open Pulse
module R = Pulse.Lib.Reference
#lang-pulse

/// The shape R3.4 emits for `[Refine("Lo <= Hi")] struct Iv { int Lo; int Hi; }`.
noeq type struct_Iv__raw = { fld_Lo: I32.t; fld_Hi: I32.t }

let struct_Iv__pred (this: struct_Iv__raw) : prop =
  I32.v this.fld_Lo <= I32.v this.fld_Hi

type struct_Iv = this: struct_Iv__raw { struct_Iv__pred this }

/// F10: module-qualified record syntax resolves in all three positions --
///      projection, update and literal -- with `StructFacts` never `open`ed by the
///      user of the record. This is why a generated function module needs no `open`
///      for the structs it mentions, and why two structs may share a field name.
///
///      The projection below is written `.StructFacts.fld_Lo` rather than `.fld_Lo`
///      precisely to exercise the qualified form; the unqualified one would resolve
///      here only because we are inside the defining module.
let qualified_projection (p: struct_Iv) : I32.t = p.StructFacts.fld_Lo

let qualified_literal (a: I32.t) (b: I32.t{I32.v a <= I32.v b}) : struct_Iv =
  { StructFacts.fld_Lo = a; fld_Hi = b }

/// The refinement is a refinement *type*, so widening re-proves it. Weaken the
/// argument's type here and this definition stops type-checking -- which is the whole
/// content of R3.4's claim that `[Refine]` costs the emitter nothing.
let qualified_update (p: struct_Iv) (v: I32.t{I32.v v >= I32.v p.StructFacts.fld_Hi})
  : struct_Iv
  = { p with StructFacts.fld_Hi = v }

/// F11: a record update's source must be a *pure* term. Writing the update as
///      `var_p := { !var_p with StructFacts.fld_Hi = v }` is rejected --
///      "Expected expression of type struct_Iv__raw, got expression of type
///      fn ... returns ..." -- because `!` is a stateful operation and `{ _ with _ }`
///      is a term former. So R3.6 let-binds the dereference first, which is the form
///      below. This does not contradict F8: F8 licenses a stateful block as the
///      scrutinee of a `let`, and that is exactly the fix.
fn struct_field_write (var_p: R.ref struct_Iv) (arg_v: I32.t)
requires exists* p. R.pts_to var_p p ** pure (I32.v arg_v >= I32.v p.fld_Hi)
ensures  exists* p. R.pts_to var_p p
{
  let cur = !var_p;
  var_p := { cur with StructFacts.fld_Hi = arg_v };
}

/// F12: a Pulse `fn` must have at least one binder. A C# method with no parameters
///      therefore takes `()`; without it Pulse fails in the elaborator rather than the
///      solver, with "main: FnDefn does not have binders".
fn no_parameters ()
requires emp
returns  r: struct_Iv
ensures  pure (I32.v r.fld_Lo == 0)
{
  ({ StructFacts.fld_Lo = 0l; fld_Hi = 0l })
}
