using PalLang;

namespace PalCSharp.Tests;

/// <summary>
/// §7.2's variant test for the Adler-32 case study: the same checksum written
/// differently, which must verify with no change to the emitter.
///
/// What is varied, relative to <see cref="Adler32"/>:
/// <list type="bullet">
/// <item>the inner loop is a <c>for</c> rather than a <c>while</c>, so its decrement
///       reaches the emitter through Normalize's desugaring instead of as a statement;</item>
/// <item>the chunk size is chosen with a conditional expression rather than an
///       <c>if</c> statement, so it is an expression the emitter must let-bind;</item>
/// <item>the accumulators are updated with compound assignments;</item>
/// <item>the outer guard is <c>!= 0</c> rather than <c>&gt; 0</c>;</item>
/// <item>every local is renamed, and the two accumulators are declared in the opposite
///       order.</item>
/// </list>
///
/// The specification is *not* varied: it is the same inductive definition of RFC 1950
/// §8.2 under different names, restated here only because a test project may not share declarations across
/// cases. That is the point — two differently written programs are proved to compute the
/// same mathematical function.
/// </summary>
public static class Adler32Variant
{
    public const uint MOD = 65521;
    public const int CHUNK = 3800;
    public const uint LOMAX = 1034520;

    [Spec(Recursive = true)]
    [Requires("0 <= off && 0 <= n && off + n <= s.Length")]
    [Decreases("n")]
    public static SpecInt Lo(Seq<byte> s, SpecInt off, SpecInt n) =>
        n == 0 ? 1 : Lo(s, off, n - 1) + s[off + n - 1];

    [Spec(Recursive = true)]
    [Requires("0 <= off && 0 <= n && off + n <= s.Length")]
    [Decreases("n")]
    public static SpecInt Hi(Seq<byte> s, SpecInt off, SpecInt n) =>
        n == 0 ? 0 : Hi(s, off, n - 1) + Lo(s, off, n);

    [Spec]
    [Requires("0 <= off && 0 <= n && off + n <= s.Length")]
    public static SpecInt Sum(Seq<byte> s, SpecInt off, SpecInt n) =>
        (Hi(s, off, n) % MOD) * 65536 + (Lo(s, off, n) % MOD);

    [Lemma]
    [Requires("0 <= off && 0 <= n && off + n + 1 <= s.Length")]
    [Ensures("Lo(s, off, n + 1) == Lo(s, off, n) + s[off + n]")]
    [Ensures("Hi(s, off, n + 1) == Hi(s, off, n) + Lo(s, off, n + 1)")]
    [System.Diagnostics.Conditional("PAL")]
    public static void Unfold(Seq<byte> s, int off, SpecInt n) { }

    [Lemma]
    [Requires("a % MOD == b % MOD")]
    [Requires("c % MOD == d % MOD")]
    [Ensures("(a + c) % MOD == (b + d) % MOD")]
    [PulseBody("FStar.Math.Lemmas.lemma_mod_add_distr $(c) $(a) 65521; "
               + "FStar.Math.Lemmas.lemma_mod_add_distr $(c) $(b) 65521; "
               + "FStar.Math.Lemmas.lemma_mod_add_distr $(b) $(c) 65521; "
               + "FStar.Math.Lemmas.lemma_mod_add_distr $(b) $(d) 65521")]
    [System.Diagnostics.Conditional("PAL")]
    public static void CongAdd(SpecInt a, SpecInt b, SpecInt c, SpecInt d) { }

    // The step of the bound on `high`: the bound grows by `LOMAX` a byte, and `low`
    // never exceeds it. Stated apart from the loop, where the solver meets it in a
    // context of sequence and modular facts and does not find the linear proof.
    [Lemma]
    [Requires("1 <= k && k <= CHUNK")]
    [Requires("low <= MOD - 1 + 255 * (CHUNK - (k - 1))")]
    [Requires("high <= MOD - 1 + (CHUNK - k) * LOMAX")]
    [Ensures("high + low <= MOD - 1 + (CHUNK - (k - 1)) * LOMAX")]
    [System.Diagnostics.Conditional("PAL")]
    public static void HighStep(SpecInt k, SpecInt low, SpecInt high) { }

    [Lemma]
    [Ensures("(a % MOD) % MOD == a % MOD")]
    [System.Diagnostics.Conditional("PAL")]
    public static void CongIdem(SpecInt a) { }

    [Requires("0 <= at && 0 <= left && at + left <= data.Length")]
    [Requires("lowIn == 1 && highIn == 0")]
    [Ensures("Contents(data) == Old(Contents(data))")]
    [Ensures("Result == Sum(Old(Contents(data)), Old(at), Old(left))")]
    public static uint Update(uint highIn, uint lowIn, byte[] data, int at, int left)
    {
        uint high = highIn;
        uint low = lowIn;
        while (left != 0)
        {
            Pal.Decreases(left);
            Pal.Invariant(0 <= at && 0 <= left && at + left <= data.Length);
            Pal.Invariant(low < MOD && high < MOD);
            Pal.Invariant(Pal.Contents(data) == Pal.Old(Pal.Contents(data)));
            Pal.Invariant(Pal.Old(at) <= at && at + left == Pal.Old(at) + Pal.Old(left));
            Pal.Invariant(low % MOD == Lo(Pal.Contents(data), Pal.Old(at), at - Pal.Old(at)) % MOD);
            Pal.Invariant(high % MOD == Hi(Pal.Contents(data), Pal.Old(at), at - Pal.Old(at)) % MOD);

            int chunk = left < CHUNK ? left : CHUNK;
            left -= chunk;
            for (int k = chunk; k > 0; k--)
            {
                Pal.Decreases(k);
                Pal.Invariant(0 <= at && 0 <= k && k <= CHUNK && 0 <= left);
                Pal.Invariant(at + k + left <= data.Length);
                Pal.Invariant(low <= MOD - 1 + 255 * (CHUNK - k));
                Pal.Invariant(high <= MOD - 1 + (CHUNK - k) * LOMAX);
                Pal.Invariant(Pal.Contents(data) == Pal.Old(Pal.Contents(data)));
                Pal.Invariant(Pal.Old(at) <= at && at + k + left == Pal.Old(at) + Pal.Old(left));
                Pal.Invariant(low % MOD == Lo(Pal.Contents(data), Pal.Old(at), at - Pal.Old(at)) % MOD);
                Pal.Invariant(high % MOD == Hi(Pal.Contents(data), Pal.Old(at), at - Pal.Old(at)) % MOD);

                Pal.GhostStmt("Pulse.Lib.Array.pts_to_len $&(data)");
                Unfold(Pal.Contents(data), Pal.Old(at), at - Pal.Old(at));
                CongAdd(low, Lo(Pal.Contents(data), Pal.Old(at), at - Pal.Old(at)),
                       Pal.Contents(data)[at], Pal.Contents(data)[at]);
                low += (uint)(data[at++] & 0xff);
                CongAdd(high, Hi(Pal.Contents(data), Pal.Old(at), at - Pal.Old(at) - 1),
                       low, Lo(Pal.Contents(data), Pal.Old(at), at - Pal.Old(at)));
                HighStep(k, low, high);
                high += low;
                // Splitting the invariant's re-establishment into its conjuncts. The
                // proof is the same one `Adler32` gives; stating the intermediate steps
                // is what keeps the query within reach of the solver here, where the
                // chunk size arrives as a conditional expression rather than through an
                // `if` statement and so is a `match` term the solver must case-split.
                Pal.Assert(low % MOD == Lo(Pal.Contents(data), Pal.Old(at), at - Pal.Old(at)) % MOD);
                Pal.Assert(high % MOD == Hi(Pal.Contents(data), Pal.Old(at), at - Pal.Old(at)) % MOD);
                Pal.Assert(at + (k - 1) + left == Pal.Old(at) + Pal.Old(left));
                Pal.Assert(low <= MOD - 1 + 255 * (CHUNK - (k - 1)));
                Pal.Assert(high <= MOD - 1 + (CHUNK - (k - 1)) * LOMAX);
            }
            CongIdem(low);
            CongIdem(high);
            low %= MOD;
            high %= MOD;
        }
        Pal.GhostStmt("assert (pure (U32.v (Cast.int32_to_uint32 16l) == 16))");
        Pal.Assert(low == Lo(Pal.Contents(data), Pal.Old(at), Pal.Old(left)) % MOD);
        Pal.Assert(high == Hi(Pal.Contents(data), Pal.Old(at), Pal.Old(left)) % MOD);
        return (high << 16) | low;
    }
}
