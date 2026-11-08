using System;

namespace PalLang;

/// <summary>
/// R32.14. Two's-complement wrapping in contracts: <c>Pulse.Lib.CSharp.Wrap</c>.
/// </summary>
public static class SpecWrap
{
    private static Exception Ghost() => new InvalidOperationException(
        "SpecWrap is a specification-only construct and has no runtime meaning.");

    /// <summary><paramref name="x"/> wrapped to a 32-bit two's-complement value, as a <c>[Wrapping]</c> <c>int</c> holds it.</summary>
    [SpecOp("Pulse.Lib.CSharp.Wrap.int32")]
    public static SpecInt Int32(SpecInt x) => throw Ghost();
}
