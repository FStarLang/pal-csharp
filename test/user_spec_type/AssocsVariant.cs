using PalLang;

namespace PalCSharp.Tests;

/// <summary>
/// §7.2's contortion detector, for §11. This file is an equivalent program to
/// <see cref="Assocs"/>, written differently on every axis the emitter could have been
/// fitted to, and it must verify with no change to the compiler:
///
/// <list type="bullet">
/// <item>every null test is at the opposite polarity, with the empty case in the
///   <c>else</c>;</item>
/// <item>the model operations are reached as instance members where <see cref="Assocs"/>
///   reached them as statics, and the reverse;</item>
/// <item>results are bound to locals before being returned;</item>
/// <item>the key comparison is written the other way round.</item>
/// </list>
/// </summary>
public static class AssocsVariant
{
    /// <summary>The empty chain, and the only place the empty constructor is named.</summary>
    [Spec]
    public static SpecAssoc<SpecInt, SpecInt> Nothing => SpecAssoc.Nil<SpecInt, SpecInt>();

    [Requires("c.Map.Count < 2147483647")]
    [Ensures("Result == c.Map.Count")]
    [Decreases("c.Map")]
    public static int Size([Frac("q")] Pair? c)
    {
        if (c != null)
        {
            int rest = Size(c.next);
            int total = rest + 1;
            return total;
        }
        return 0;
    }

    /// <summary>
    /// The same traversal as <c>Assocs.Get</c>, with the branches swapped and the
    /// comparison reversed.
    /// </summary>
    [Ensures("Result == c.Map.Get(k, 0)")]
    [Decreases("c.Map")]
    public static int Lookup([Frac("q")] Pair? c, int k)
    {
        if (c != null)
        {
            if (k == c.key)
            {
                int here = c.val;
                return here;
            }
            int deeper = Lookup(c.next, k);
            return deeper;
        }
        return 0;
    }

    /// <summary>
    /// A destructive update whose empty case is the <c>else</c>, and whose recursive arm
    /// comes first. R5.4: each arm ends in its own <c>return</c>.
    /// </summary>
    [Ensures("c.Map == SpecAssoc.Set(Old(c.Map), k, value)")]
    [Decreases("c.Map")]
    public static void Update(Pair? c, int k, int value)
    {
        if (c != null)
        {
            if (k != c.key)
            {
                Update(c.next, k, value);
                return;
            }
            else
            {
                c.val = value;
                return;
            }
        }
        else
        {
            return;
        }
    }
}
