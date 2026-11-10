module Pulse.Lib.CSharp.Enumerable
#lang-pulse

/// `System.Collections.Generic.IEnumerable<T>` and `ICollection<T>`, as a method's
/// *argument* (doc/translation.md §34).
///
/// An argument typed by one of these interfaces is a value the method only reads. It
/// is a resource, `pts_to e #p s`, owned by the caller and lent for the call, and not
/// a pure sequence: the caller could hand the method a view of an object the method
/// itself changes (`list.AddRange(list.Where(...))`), and a pure model would let the
/// method prove a postcondition that the CLR's own version check refutes. Separate
/// ownership makes that call unprovable instead (R34.2).
///
/// Whether the object also implements `ICollection<T>` is `is_collection`, which is
/// abstract: a method that tests it is verified in both branches, and the two must
/// meet one postcondition (R34.4).
///
/// An enumerator is a *cursor*: the number of items it has yielded, held in a C#
/// `int` cell. `MoveNext` and `Current` are `move_next` and `current` below (R34.6).
///
/// The functions here are implemented (in the `.fst`) over a read-only array, so the
/// interface carries no assumption of its own; what the translation trusts about a
/// real `IEnumerable<T>` -- that enumeration yields exactly the items, terminates and
/// has no effect -- is stated once, in §34.

open Pulse
module A = Pulse.Lib.CSharp.Array.Base
module R = Pulse.Lib.Reference
module I32 = FStar.Int32
module Seq = FStar.Seq
module CS = Pulse.Lib.CSharp.Seq
module KM = Pulse.Lib.CSharp.KeyMap
module T = FStar.Tactics.V2

val enumerable (t: Type0) : Type0

val pts_to (#t: Type0) ([@@@mkey] e: enumerable t)
  (#[T.exact (`1.0R)] p: perm) (s: Seq.seq t) : slprop

/// An enumerable's items are counted by an `int` (`ICollection<T>.Count`).
ghost
fn pts_to_len (#t: Type0) (e: enumerable t) (#p: perm) (#s: Seq.seq t)
  preserves pts_to e #p s
  ensures pure (Seq.length s < pow2 31)

/// `e is ICollection<T>`.
val is_collection (#t: Type0) (e: enumerable t) : bool

/// `((ICollection<T>)e).Count`.
fn count (#t: Type0) (e: enumerable t { is_collection e })
  (#p: perm) (#s: Ghost.erased (Seq.seq t))
  preserves pts_to e #p s
  returns n: I32.t
  ensures pure (I32.v n == Seq.length s)

/// `((ICollection<T>)e).CopyTo(dst, i)`. The CLR throws when the items do not fit;
/// here that is the caller's obligation.
fn copy_to (#t: Type0) (e: enumerable t { is_collection e }) (dst: A.array t) (i: I32.t)
  (#p: perm) (#s: Ghost.erased (Seq.seq t))
  (#d: Ghost.erased (Seq.seq t) { I32.v i >= 0 /\ I32.v i + Seq.length s <= Seq.length d })
  preserves pts_to e #p s
  requires A.pts_to dst d
  ensures A.pts_to dst (CS.copied_at s 0 d (I32.v i) (Seq.length s))

/// R34.22. `d.Keys.CopyTo(dst, i)` on an `IDictionary<K, V>` argument, an enumerable of
/// its pairs: the keys, in the order the pairs enumerate.
fn copy_keys (#a #b: Type0) (e: enumerable (a & b)) (dst: A.array a) (i: I32.t)
  (#p: perm) (#s: Ghost.erased (Seq.seq (a & b)))
  (#d: Ghost.erased (Seq.seq a) { I32.v i >= 0 /\ I32.v i + Seq.length s <= Seq.length d })
  preserves pts_to e #p s
  requires A.pts_to dst d
  ensures A.pts_to dst (CS.copied_at (KM.keys s) 0 d (I32.v i) (Seq.length s))

/// R34.22. `d.Values.CopyTo(dst, i)`, in the same order.
fn copy_values (#a #b: Type0) (e: enumerable (a & b)) (dst: A.array b) (i: I32.t)
  (#p: perm) (#s: Ghost.erased (Seq.seq (a & b)))
  (#d: Ghost.erased (Seq.seq b) { I32.v i >= 0 /\ I32.v i + Seq.length s <= Seq.length d })
  preserves pts_to e #p s
  requires A.pts_to dst d
  ensures A.pts_to dst (CS.copied_at (KM.values s) 0 d (I32.v i) (Seq.length s))

/// The cursor after one `MoveNext`: one further, unless every item has been yielded.
let advance (#t: Type0) (s: Seq.seq t) (k: I32.t) : I32.t =
  if I32.v k < Seq.length s && I32.v k < 2147483647 then I32.add k 1l else k

/// `en.MoveNext()`, for the enumerator of `e` whose cursor is `r`.
fn move_next (#t: Type0) (e: enumerable t) (r: R.ref I32.t)
  (#p: perm) (#s: Ghost.erased (Seq.seq t)) (#k: Ghost.erased I32.t)
  preserves pts_to e #p s
  requires R.pts_to r k
  returns b: bool
  ensures R.pts_to r (advance s k) ** pure (b == (I32.v k < Seq.length s) /\ Seq.length s < pow2 31)

/// `en.Current`, defined only after a `MoveNext` that returned `true`.
fn current (#t: Type0) (e: enumerable t) (r: R.ref I32.t)
  (#p: perm) (#s: Ghost.erased (Seq.seq t))
  (#k: Ghost.erased I32.t { 1 <= I32.v k /\ I32.v k <= Seq.length s })
  preserves pts_to e #p s ** R.pts_to r k
  returns x: t
  ensures rewrites_to x (Seq.index s (I32.v k - 1))

/// An array's items, lent as an enumerable that is, or is not, an `ICollection<T>`: a
/// caller holding the array can pass it, and get it back unchanged.
val view (#t: Type0) (a: A.array t) (coll: bool) : e: enumerable t { is_collection e == coll }

ghost
fn lend (#t: Type0) (a: A.array t) (coll: bool) (#p: perm) (#s: Seq.seq t)
  requires A.pts_to a #p s
  ensures pts_to (view a coll) #p s

ghost
fn unlend (#t: Type0) (a: A.array t) (coll: bool) (#p: perm) (#s: Seq.seq t)
  requires pts_to (view a coll) #p s
  ensures A.pts_to a #p s
