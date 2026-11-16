using PalLang;

// The bitmap `BitHelper` keeps over a span of `int`s, as dotnet/runtime#133116's
// SortedSet<T>.CheckUniqueAndUnfoundElements uses it (doc/translation.md §37, R37.2).
[assembly: IncludePulseFile("BitHelperBits.fst")]

namespace System.Collections.Generic
{
    internal static class BitHelperBits
    {
        private static Exception Ghost() => new InvalidOperationException(
            "BitHelperBits is a specification-only construct and has no runtime meaning.");

        // Bit `p` of the words is bit `p % 32` of word `p / 32`.
        [SpecOp("BitHelperBits.bits")]
        internal static Seq<bool> Bits(Seq<int> ws) => throw Ghost();

        [SpecOp("BitHelperBits.zero")]
        internal static bool Zero(Seq<int> ws) => throw Ghost();

        // The words after `MarkBit(p)`, and what `IsMarked(p)` returns.
        [SpecOp("BitHelperBits.set_bit")]
        internal static Seq<int> SetBit(Seq<int> ws, SpecInt p) => throw Ghost();

        [SpecOp("BitHelperBits.marked")]
        internal static bool Marked(Seq<int> ws, SpecInt p) => throw Ghost();

        // Zero words hold no bit; `MarkBit(p)` sets bit `p` alone; `IsMarked(p)` reads it.
        [SpecOp("BitHelperBits.zero_bits")]
        internal static void ZeroBits(Seq<int> ws) => throw Ghost();

        [SpecOp("BitHelperBits.set_bits")]
        internal static void SetBits(Seq<int> ws, SpecInt p) => throw Ghost();

        [SpecOp("BitHelperBits.marked_bits")]
        internal static void MarkedBits(Seq<int> ws, SpecInt p) => throw Ghost();

        // Both at any position: past the words, `IsMarked` reads false and `MarkBit` does nothing.
        [SpecOp("BitHelperBits.bits_at")]
        internal static void BitsAt(Seq<int> ws, SpecInt p) => throw Ghost();

        // `ToIntArrayLength(n)` words hold at least `n` bits.
        [SpecOp("BitHelperBits.words_cover")]
        internal static void WordsCover(SpecInt n) => throw Ghost();
    }
}
