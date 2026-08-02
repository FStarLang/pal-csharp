// A Roslyn analyzer is loaded into whatever process is doing the compiling, and that
// process may be .NET Framework, so an analyzer assembly and everything it drags with it
// must be `netstandard2.0`.  Nothing in pal-csharp needs a newer *runtime*: what the
// compiler uses and netstandard2.0 lacks is six language and BCL conveniences, and they
// are all one file's worth of shim.  This file is that file, and it is `#if`'d so the
// net10.0 build sees none of it.
//
// Note that `LangVersion` is independent of the target framework: records, pattern
// matching, collection expressions and nullable annotations all work here, which is why
// the retarget touches no real code.

#if NETSTANDARD2_0
using System;
using System.Collections.Generic;

namespace System.Runtime.CompilerServices
{
    internal static class IsExternalInit { }
}

namespace System
{
    internal readonly struct Index : IEquatable<Index>
    {
        private readonly int _value;
        public Index(int value, bool fromEnd = false) => _value = fromEnd ? ~value : value;
        public int Value => _value < 0 ? ~_value : _value;
        public bool IsFromEnd => _value < 0;
        public int GetOffset(int length) => IsFromEnd ? length - Value : Value;
        public static implicit operator Index(int value) => new Index(value);
        public bool Equals(Index other) => _value == other._value;
        public override bool Equals(object? o) => o is Index i && Equals(i);
        public override int GetHashCode() => _value;
    }

    internal readonly struct Range
    {
        public Index Start { get; }
        public Index End { get; }
        public Range(Index start, Index end) { Start = start; End = end; }
        public static Range StartAt(Index start) => new Range(start, new Index(0, true));
        public static Range EndAt(Index end) => new Range(new Index(0), end);
        public static Range All => new Range(new Index(0), new Index(0, true));
        public (int Offset, int Length) GetOffsetAndLength(int length)
        {
            var s = Start.GetOffset(length);
            var e = End.GetOffset(length);
            return (s, e - s);
        }
    }
}

namespace System.Runtime.CompilerServices
{
    internal static class RuntimeHelpersPolyfill
    {
        public static T[] GetSubArray<T>(T[] array, Range range)
        {
            var (offset, length) = range.GetOffsetAndLength(array.Length);
            var result = new T[length];
            Array.Copy(array, offset, result, 0, length);
            return result;
        }
    }
}

namespace Pal.Compiler
{
    internal static class Polyfills
    {
        public static void Deconstruct<TK, TV>(this KeyValuePair<TK, TV> pair, out TK key, out TV value)
        {
            key = pair.Key;
            value = pair.Value;
        }

        public static string[] Split(this string s, char separator, StringSplitOptions options = StringSplitOptions.None) =>
            s.Split(new[] { separator }, options);

        public static string[] Split(this string s, string separator, StringSplitOptions options = StringSplitOptions.None) =>
            s.Split(new[] { separator }, options);

        public static bool Contains(this string s, char c) => s.IndexOf(c) >= 0;

        public static bool StartsWith(this string s, char c) => s.Length > 0 && s[0] == c;

        public static bool EndsWith(this string s, char c) => s.Length > 0 && s[s.Length - 1] == c;
    }
}
#endif
