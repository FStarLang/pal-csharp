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

/// R13.4's promotion, and the fact that makes it usable.
///
/// `b & 0xff` on a `byte` is written all over byte-oriented C# as a defence against a
/// sign extension that cannot occur, and C# evaluates it at `int` width: both operands
/// are promoted, `int`'s `&` is applied, and the result is an `int`. The mask is
/// therefore the identity, but saying so means relating `FStar.Int`'s bitwise
/// operations to `FStar.UInt`'s, which no ulib lemma does.
///
/// This belongs in the library rather than in any one program's annotations because the
/// idiom belongs to the language, not to the program: every checksum, decoder and parser
/// in C# writes it.
val byte_mask_ff (b: FStar.UInt8.t)
  : Lemma (FStar.Int32.v (FStar.Int32.logand (uint8_to_int32 b) 255l) == FStar.UInt8.v b)

/// The same fact in the form an overflow obligation consumes: a masked byte, cast back
/// to `uint` as C# does before adding it to an accumulator, is at most 255.
/// The trigger is the idiom itself, so a program that writes `(uint)(b & 0xff)` needs
/// no annotation to be told what it computes.
val byte_mask_ff_bound (b: FStar.UInt8.t)
  : Lemma (FStar.UInt32.v (int32_to_uint32 (FStar.Int32.logand (uint8_to_int32 b) 255l))
           == FStar.UInt8.v b)
          [SMTPat (int32_to_uint32 (FStar.Int32.logand (uint8_to_int32 b) 255l))]

/// Packing two halves of a word — `(hi << m) | lo` — is how C# writes a composite value
/// into a single integer, and it is the shape every checksum, colour value and packed
/// flag field takes. It denotes ordinary arithmetic exactly when the two halves do not
/// overlap, which is what the precondition says: `hi` must still fit after the shift,
/// and `lo` must fit below it.
///
/// The trigger is the idiom itself, so the arithmetic reading is available wherever the
/// program writes the shift-or, with no annotation. The lemma is stated over an
/// arbitrary shift amount rather than a literal because C# writes the amount as an
/// `int`, and R13.5's bridge means the emitted term is a conversion, never a literal.
val logor_shift_disjoint (x y m: FStar.UInt32.t)
  : Lemma (requires 0 < FStar.UInt32.v m /\ FStar.UInt32.v m < 32 /\
                    FStar.UInt32.v x < pow2 (32 - FStar.UInt32.v m) /\
                    FStar.UInt32.v y < pow2 (FStar.UInt32.v m))
          (ensures FStar.UInt32.v (FStar.UInt32.logor (FStar.UInt32.shift_left x m) y) ==
                   FStar.UInt32.v x * pow2 (FStar.UInt32.v m) + FStar.UInt32.v y)
          [SMTPat (FStar.UInt32.logor (FStar.UInt32.shift_left x m) y)]
