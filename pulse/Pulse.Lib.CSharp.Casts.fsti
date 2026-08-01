module Pulse.Lib.CSharp.Casts

/// The `int`/`size_t` bridge.
///
/// C# array and `Span<T>` indices are *signed* 32-bit `int`, while Pulse arrays
/// are indexed by `size_t`. Rather than let that conversion appear ad hoc at
/// every subscript, the translation scheme (doc/translation.md, R3.3) fixes a
/// single canonical bridge, `idx`, and uses it everywhere.

include FStar.Int.Cast

module I32 = FStar.Int32
module SZ = FStar.SizeT

val int32_to_sizet (x: I32.t) : Pure SZ.t
  (requires I32.v x >= 0)
  (ensures fun y -> SZ.v y == I32.v x)

val sizet_to_int32 (x: SZ.t) : Pure I32.t
  (requires SZ.v x < pow2 31)
  (ensures fun y -> I32.v y == SZ.v x)

/// The canonical index bridge. Every C# subscript `a[i]` translates to a Pulse
/// access at `idx i`, and the emitter emits the obligation `0 <= i` alongside.
unfold
let idx (i: I32.t { I32.v i >= 0 }) : SZ.t = int32_to_sizet i
