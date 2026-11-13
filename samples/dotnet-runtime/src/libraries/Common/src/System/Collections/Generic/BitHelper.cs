// Licensed to the .NET Foundation under one or more agreements.
// The .NET Foundation licenses this file to you under the MIT license.

using System.Diagnostics;
using PalLang;

namespace System.Collections.Generic
{
    // pal: R17.10. A ref struct over one span is that span: `MarkBit` and `IsMarked` are
    // functions of it, `_span` (and `Span`) name it. Its bits are `BitHelperBits.Bits`.
    internal ref struct BitHelper
    {
        private const int IntSize = sizeof(int) * 8;
        private readonly Span<int> _span;

        internal Span<int> Span => _span;

        [Ensures("Pal.Contents(span).Length == Pal.Old(Pal.Contents(span)).Length")]
        [Ensures("Pal.Implies(clear, BitHelperBits.Zero(Pal.Contents(span)))")]
        [Ensures("Pal.Implies(!clear, Pal.Contents(span) == Pal.Old(Pal.Contents(span)))")]
        internal BitHelper(Span<int> span, bool clear)
        {
            if (clear)
            {
                span.Clear();
            }
            _span = span;
        }

        // pal: R34.12. `1 << 31` is `int.MinValue`, as C#'s unchecked shift computes it.
        [Requires("bitPosition >= 0")]
        [Ensures("Pal.Contents(@this.Span) == BitHelperBits.SetBit(Pal.Old(Pal.Contents(@this.Span)), bitPosition)")]
        [Wrapping]
        internal void MarkBit(int bitPosition)
        {
            Debug.Assert(bitPosition >= 0);

            uint bitArrayIndex = (uint)bitPosition / IntSize;

            // Workaround for https://github.com/dotnet/runtime/issues/72004
            Span<int> span = _span;
            if (bitArrayIndex < (uint)span.Length)
            {
                span[(int)bitArrayIndex] |= (1 << (int)((uint)bitPosition % IntSize));
            }
        }

        [Requires("bitPosition >= 0")]
        [Ensures("Result == BitHelperBits.Marked(Pal.Contents(@this.Span), bitPosition)")]
        [Ensures("Pal.Contents(@this.Span) == Pal.Old(Pal.Contents(@this.Span))")]
        [Wrapping]
        internal bool IsMarked(int bitPosition)
        {
            Debug.Assert(bitPosition >= 0);

            uint bitArrayIndex = (uint)bitPosition / IntSize;

            // Workaround for https://github.com/dotnet/runtime/issues/72004
            ReadOnlySpan<int> span = _span;
            return
                bitArrayIndex < (uint)span.Length &&
                (span[(int)bitArrayIndex] & (1 << ((int)((uint)bitPosition % IntSize)))) != 0;
        }

        /// <summary>How many ints must be allocated to represent n bits. Returns (n+31)/32, but avoids overflow.</summary>
        [Ensures("Result == (n > 0 ? (n - 1) / 32 + 1 : 0)")]
        internal static int ToIntArrayLength(int n) => n > 0 ? ((n - 1) / IntSize + 1) : 0;
    }
}
