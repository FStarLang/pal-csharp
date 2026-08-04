using PalLang;

namespace PalCSharp.Tests;

/// <summary>
/// §10's client rules over a §11 model type. Every proof step in the generated Pulse is
/// one §10 already placed — the case lemma before the null test, the window in the `else`
/// branch, the closing `intro_cons` — and none of it knows what `UserAssoc.assoc` is.
/// </summary>
public static class Assocs
{
    /// <summary>
    /// R10.7 at a three-argument constructor. The traversal is written exactly as
    /// <c>Lists.Length</c> is; what differs is only the model the postcondition names.
    /// </summary>
    [Requires("m.Map.Count < 2147483647")]
    [Ensures("Result == m.Map.Count")]
    [Decreases("m.Map")]
    public static int Count([Frac("p")] Pair? m)
    {
        if (m == null)
        {
            return 0;
        }
        return 1 + Count(m.next);
    }

    /// <summary>
    /// R10.6a. Allocation, through the constructor. The postcondition is the user's own
    /// constructor applied to the user's own model.
    /// </summary>
    [Ensures("Result.Map == SpecAssoc.Entry<SpecInt, SpecInt>(k, v, rest.Map)")]
    public static Pair Add(int k, int v, [Consumes] Pair? rest)
    {
        return new Pair(k, v, rest);
    }

    /// <summary>
    /// R10.6b, and the case that makes the two pure arguments matter: the write changes
    /// the *second* one, so the closing <c>intro_cons</c> re-establishes the invariant at
    /// a model whose first pure equation is unchanged and whose second is not.
    ///
    /// <para>R5.4. Each arm ends in its own <c>return</c>, because they leave the object
    /// in different states.</para>
    /// </summary>
    [Ensures("m.Map == SpecAssoc.Set(Old(m.Map), key, x)")]
    [Decreases("m.Map")]
    public static void Set(Pair? m, int key, int x)
    {
        if (m == null)
        {
            return;
        }
        if (m.key == key)
        {
            m.val = x;
            return;
        }
        Set(m.next, key, x);
    }

    /// <summary>
    /// A read that goes through the model's own operations rather than the class's, which
    /// is what a user-defined specification type is <em>for</em>: the postcondition is
    /// stated in the user's F* theory, and the proof is the library's.
    /// </summary>
    [Ensures("Result == m.Map.Get(key, 0)")]
    [Decreases("m.Map")]
    public static int Get([Frac("p")] Pair? m, int key)
    {
        if (m == null)
        {
            return 0;
        }
        if (m.key == key)
        {
            return m.val;
        }
        return Get(m.next, key);
    }
}
