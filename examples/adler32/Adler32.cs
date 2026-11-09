using PalLang;

namespace PalCSharp.Tests;

/// <summary>
/// Adler-32, ported from SharpZipLib
/// (<c>src/ICSharpCode.SharpZipLib/Checksum/Adler32.cs</c>, MIT).
///
/// This is the first pal-csharp case study on production code rather than on an example
/// written to be verified, and it was chosen for one reason: the code carries a
/// hand-written safety argument in a comment, so there is something specific to check
/// rather than merely a definition to restate.
///
/// <code>
/// // We can defer the modulo operation:
/// // s1 maximally grows from 65521 to 65521 + 255 * 3800
/// // s2 maximally grows by 3800 * median(s1) = 2090079800 &lt; 2^31
/// </code>
///
/// The conclusion is right and the figure is wrong. The true supremum of <c>s2</c> is
/// 2090626020 — larger than the comment's 2090079800 by 546220 — because "median(s1)"
/// approximates a triangular sum. The comment therefore *understates* the maximum, which
/// is the direction that would have mattered had the margin been thinner; against the
/// 2^31 the comment aims at, the real headroom is 2.65%, not 2.68%. See
/// <c>test/pulse_facts/ConversionFacts.fst</c>, where the arithmetic is checked.
///
/// Two adaptations to the signature, both mechanical:
/// <c>ArraySegment&lt;byte&gt;</c> is spelled out as <c>(buf, offset, count)</c>, and the
/// instance field <c>checkValue</c> is passed and returned rather than mutated. Neither
/// touches the loop, which is reproduced statement for statement.
/// </summary>
public static class Adler32
{
    /// <summary>Largest prime smaller than 65536.</summary>
    public const uint BASE = 65521;

    /// <summary>
    /// The number of bytes processed before the modulo is applied. This is the constant
    /// the comment's argument is about, so it is reproduced exactly.
    /// </summary>
    public const int NMAX = 3800;

    // ---------------------------------------------------------------------
    // The specification: RFC 1950 §8.2, stated inductively.
    // ---------------------------------------------------------------------

    /// <summary>
    /// <c>s1</c> over the first <c>n</c> bytes, unreduced: <c>1 + a[0] + … + a[n-1]</c>.
    /// </summary>
    [Spec(Recursive = true)]
    [Requires("0 <= off && 0 <= n && off + n <= s.Length")]
    [Decreases("n")]
    public static SpecInt A1(Seq<byte> s, SpecInt off, SpecInt n) =>
        n == 0 ? 1 : A1(s, off, n - 1) + s[off + n - 1];

    /// <summary>
    /// <c>s2</c> over the first <c>n</c> bytes, unreduced: the running total of
    /// <see cref="A1"/>. Expanding it gives RFC 1950's closed form
    /// <c>n + Σ (n-i+1)·a[i-1]</c>; the running-total form is used here because it is
    /// what the loop actually computes, one addition per iteration.
    /// </summary>
    [Spec(Recursive = true)]
    [Requires("0 <= off && 0 <= n && off + n <= s.Length")]
    [Decreases("n")]
    public static SpecInt A2(Seq<byte> s, SpecInt off, SpecInt n) =>
        n == 0 ? 0 : A2(s, off, n - 1) + A1(s, off, n);

    /// <summary>The packed checksum: the high half is <c>s2</c>, the low half <c>s1</c>.</summary>
    [Spec]
    [Requires("0 <= off && 0 <= n && off + n <= s.Length")]
    public static SpecInt Adler(Seq<byte> s, SpecInt off, SpecInt n) =>
        (A2(s, off, n) % BASE) * 65536 + (A1(s, off, n) % BASE);

    // ---------------------------------------------------------------------
    // Lemmas.
    // ---------------------------------------------------------------------

    /// <summary>One unfolding of each accumulator, which F* will not perform under a
    /// loop invariant by itself.</summary>
    [Lemma]
    [Requires("0 <= off && 0 <= n && off + n + 1 <= s.Length")]
    [Ensures("A1(s, off, n + 1) == A1(s, off, n) + s[off + n]")]
    [Ensures("A2(s, off, n + 1) == A2(s, off, n) + A1(s, off, n + 1)")]
    [System.Diagnostics.Conditional("PAL")]
    public static void Step(Seq<byte> s, int off, SpecInt n) { }

    /// <summary>
    /// Reducing early is the same as reducing late — the fact that licenses the deferred
    /// modulo. The loop keeps <c>s1</c> and <c>s2</c> reduced at every chunk boundary
    /// while the specification reduces only at the end, so what the loop maintains is not
    /// equality with the specification but *congruence* to it. Congruence survives both
    /// operations the loop performs: adding a byte, and reducing.
    /// </summary>
    [Lemma]
    [Requires("a % BASE == b % BASE")]
    [Requires("c % BASE == d % BASE")]
    [Ensures("(a + c) % BASE == (b + d) % BASE")]
    [PulseBody("FStar.Math.Lemmas.lemma_mod_add_distr $(c) $(a) 65521; "
               + "FStar.Math.Lemmas.lemma_mod_add_distr $(c) $(b) 65521; "
               + "FStar.Math.Lemmas.lemma_mod_add_distr $(b) $(c) 65521; "
               + "FStar.Math.Lemmas.lemma_mod_add_distr $(b) $(d) 65521")]
    [System.Diagnostics.Conditional("PAL")]
    public static void ModAdd(SpecInt a, SpecInt b, SpecInt c, SpecInt d) { }

    /// <summary>Reducing twice is reducing once.</summary>
    [Lemma]
    [Ensures("(a % BASE) % BASE == a % BASE")]
    [System.Diagnostics.Conditional("PAL")]
    public static void ModIdem(SpecInt a) { }

    // ---------------------------------------------------------------------
    // The implementation.
    // ---------------------------------------------------------------------

    /// <summary>
    /// The largest value <c>s1</c> can reach before the deferred modulo is applied:
    /// <c>BASE - 1 + 255 * NMAX</c>. This is the comment's first claim, and it is right.
    /// </summary>
    public const uint S1MAX = 1034520;

    /// <summary>One byte's worth of the comment's first claim: <c>s1</c> gains at most 255.</summary>
    [Lemma]
    [Requires("1 <= n && n <= NMAX && 0 <= b && b <= 255")]
    [Requires("s1 <= BASE - 1 + 255 * (NMAX - n)")]
    [Ensures("s1 + b <= BASE - 1 + 255 * (NMAX - (n - 1))")]
    [System.Diagnostics.Conditional("PAL")]
    public static void S1Step(SpecInt n, SpecInt s1, SpecInt b) { }

    /// <summary>
    /// One byte's worth of the comment's second claim: <c>s2</c>'s bound grows by
    /// <see cref="S1MAX"/>, and <c>s1</c> never exceeds it. Stated apart from the loop,
    /// where the solver meets it among sequence and modular facts and does not find the
    /// linear proof on its own.
    /// </summary>
    [Lemma]
    [Requires("1 <= n && n <= NMAX")]
    [Requires("s1 <= BASE - 1 + 255 * (NMAX - (n - 1))")]
    [Requires("s2 <= BASE - 1 + (NMAX - n) * S1MAX")]
    [Ensures("s2 + s1 <= BASE - 1 + (NMAX - (n - 1)) * S1MAX")]
    [System.Diagnostics.Conditional("PAL")]
    public static void S2Step(SpecInt n, SpecInt s1, SpecInt s2) { }

    [Requires("0 <= offset && 0 <= count && offset + count <= buf.Length")]
    [Requires("s1In == 1 && s2In == 0")]
    [Ensures("Contents(buf) == Old(Contents(buf))")]
    [Ensures("Result == Adler(Old(Contents(buf)), Old(offset), Old(count))")]
    public static uint Update(uint s1In, uint s2In, byte[] buf, int offset, int count)
    {
        uint s1 = s1In;
        uint s2 = s2In;
        while (count > 0)
        {
            Pal.Decreases(count);
            Pal.Invariant(0 <= offset && 0 <= count && offset + count <= buf.Length);
            Pal.Invariant(s1 < BASE && s2 < BASE);
            Pal.Invariant(Pal.Contents(buf) == Pal.Old(Pal.Contents(buf)));
            Pal.Invariant(Pal.Old(offset) <= offset && offset + count == Pal.Old(offset) + Pal.Old(count));
            // What the loop maintains is congruence, not equality: `s1` has been reduced
            // at every chunk boundary and the specification has not been reduced at all.
            Pal.Invariant(s1 % BASE == A1(Pal.Contents(buf), Pal.Old(offset), offset - Pal.Old(offset)) % BASE);
            Pal.Invariant(s2 % BASE == A2(Pal.Contents(buf), Pal.Old(offset), offset - Pal.Old(offset)) % BASE);

            // We can defer the modulo operation:
            // s1 maximally grows from 65521 to 65521 + 255 * 3800
            // s2 maximally grows by 3800 * median(s1) = 2090079800 < 2^31
            int n = NMAX;
            if (n > count)
            {
                n = count;
            }
            count -= n;
            while (n > 0)
            {
                Pal.Decreases(n);
                Pal.Invariant(0 <= offset && 0 <= n && n <= NMAX && 0 <= count);
                Pal.Invariant(offset + n + count <= buf.Length);
                // The comment's claim, made precise and made an obligation. `s1` gains at
                // most 255 per byte and there are at most NMAX bytes before the modulo;
                // `s2` gains at most `s1` per byte. Both bounds are linear in the work
                // remaining, which is what lets each one survive a single iteration.
                Pal.Invariant(s1 <= BASE - 1 + 255 * (NMAX - n));
                Pal.Invariant(s2 <= BASE - 1 + (NMAX - n) * S1MAX);
                Pal.Invariant(Pal.Contents(buf) == Pal.Old(Pal.Contents(buf)));
                Pal.Invariant(Pal.Old(offset) <= offset && offset + n + count == Pal.Old(offset) + Pal.Old(count));
                Pal.Invariant(s1 % BASE == A1(Pal.Contents(buf), Pal.Old(offset), offset - Pal.Old(offset)) % BASE);
                Pal.Invariant(s2 % BASE == A2(Pal.Contents(buf), Pal.Old(offset), offset - Pal.Old(offset)) % BASE);

                // `buf.Length` is an `int`, so it is below 2^31 and `offset + 1` cannot
                // overflow — but the invariant speaks of the *sequence's* length, and
                // nothing ties that to the array's until the two are identified here.
                Pal.GhostStmt("Pulse.Lib.CSharp.Array.pts_to_len $&(buf)");
                Step(Pal.Contents(buf), Pal.Old(offset), offset - Pal.Old(offset));
                ModAdd(s1, A1(Pal.Contents(buf), Pal.Old(offset), offset - Pal.Old(offset)),
                       Pal.Contents(buf)[offset], Pal.Contents(buf)[offset]);
                S1Step(n, s1, Pal.Contents(buf)[offset]);
                s1 = s1 + (uint)(buf[offset++] & 0xff);
                // `s1` is only *congruent* to the specification's unreduced accumulator,
                // never equal to it, so the step that adds `s1` to `s2` must be justified
                // by congruence on both summands — which is what the first `ModAdd` above
                // has just established for `s1`.
                ModAdd(s2, A2(Pal.Contents(buf), Pal.Old(offset), offset - Pal.Old(offset) - 1),
                       s1, A1(Pal.Contents(buf), Pal.Old(offset), offset - Pal.Old(offset)));
                S2Step(n, s1, s2);
                s2 = s2 + s1;
                n--;
            }
            ModIdem(s1);
            ModIdem(s2);
            s1 %= BASE;
            s2 %= BASE;
        }
        Pal.GhostStmt("assert (pure (U32.v (Cast.int32_to_uint32 16l) == 16))");
        Pal.Assert(s1 == A1(Pal.Contents(buf), Pal.Old(offset), Pal.Old(count)) % BASE);
        Pal.Assert(s2 == A2(Pal.Contents(buf), Pal.Old(offset), Pal.Old(count)) % BASE);
        return (s2 << 16) | s1;
    }
}
