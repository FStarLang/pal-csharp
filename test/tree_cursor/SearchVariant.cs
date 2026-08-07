using PalLang;

namespace PalCSharp.Tests;

/// <summary>
/// §7.2's variant of <see cref="Search"/>: the same three functions, written independently
/// and differently, verifying with no translator change.
///
/// <para>What is varied is chosen to press on the parts of the cursor scheme that could
/// plausibly have been fitted to <c>Search.cs</c>:</para>
/// <list type="bullet">
///   <item><see cref="Contains"/> answers a <em>different question</em> — membership rather
///     than the value — so the loop carries a <c>bool</c> rather than a <c>T</c> and its
///     postcondition lands on <c>SpecTree.HasKey</c>. The descent underneath is the same,
///     which is the claim: the cursor is not tied to what the loop is computing.</item>
///   <item>The comparison is spelled the other way round (<c>nk &lt; key</c> rather than
///     <c>key &gt; nk</c>) and the three-way test is nested differently — the equality case
///     is checked <em>last</em>, after both inequalities, so the two <c>DescentProof</c>
///     steps sit in the opposite arms from <c>Search.Find</c>.</item>
///   <item>The exit flag counts down from a <c>bool</c>-like <c>1</c> in
///     <see cref="Search.Find"/>; here it is written as <c>going</c> and the loop condition
///     is <c>going == 1</c> rather than <c>live != 0</c>.</item>
///   <item><see cref="Build"/> assembles a three-node tree bottom-up in a different order,
///     with the two leaves allocated inline in the argument list rather than bound first.</item>
/// </list>
/// </summary>
public static class SearchVariant
{
    /// <summary>
    /// A three-node tree, built by nesting the calls rather than naming each node. It exists
    /// so the descent below has something with a genuine left and right branch to descend
    /// through, and it pins that <see cref="Search.Node"/> composes with itself.
    /// </summary>
    [Ensures("Descent.Holds(Result, " +
             "SpecTree.Branch(SpecTree.Branch(SpecTree.Leaf<SpecKv<T>>(), " +
             "                                SpecTree.Entry(lo, a), " +
             "                                SpecTree.Leaf<SpecKv<T>>()), " +
             "                SpecTree.Entry(mid, b), " +
             "                SpecTree.Branch(SpecTree.Leaf<SpecKv<T>>(), " +
             "                                SpecTree.Entry(hi, c), " +
             "                                SpecTree.Leaf<SpecKv<T>>())))")]
    public static Knot<T> Build<T>(int lo, T a, int mid, T b, int hi, T c)
    {
        Knot<T>? none = Search.Empty<T>();
        Knot<T>? other = Search.Empty<T>();
        Knot<T> small = Search.Node(lo, a, none, other);
        Knot<T>? nil = Search.Empty<T>();
        Knot<T>? nil2 = Search.Empty<T>();
        Knot<T> large = Search.Node(hi, c, nil, nil2);
        return Search.Node(mid, b, small, large);
    }

    /// <summary>
    /// Whether the tree holds <paramref name="key"/> at all.
    ///
    /// <para>The loop is <see cref="Search.Find"/>'s with a different payload and the
    /// branches in a different order, and it needs the same six invariant clauses and the
    /// same seven lemma calls. That is the point of a variant test: had any of those been
    /// shaped by the first program rather than by the rule, this one would not go
    /// through.</para>
    /// </summary>
    [Requires("Descent.Holds(root, t)")]
    [Requires("t.Size < 2147483647")]
    [Ensures("Descent.Holds(root, t)")]
    [Ensures("Result == SpecTree.HasKey(t, key)")]
    public static bool Contains<T>(Knot<T>? root, int key, Ghost<SpecTree<SpecKv<T>>> t = default)
    {
        DescentProof.Start(root, key, t);
        int steps = 0;
        Knot<T>? at = root;
        bool answer = false;
        int going = 1;
        while (going == 1)
        {
            Pal.Invariant(Descent.Spine(root, at, Descent.Ctx(t.Value, key, steps)));
            Pal.Invariant(Descent.Holds(at, Descent.Sub(t.Value, key, steps)));
            Pal.Invariant(0 <= steps && (going == 0 || going == 1));
            Pal.Invariant(t.Value.Size < 2147483647);
            Pal.Invariant(steps + Descent.Sub(t.Value, key, steps).Size <= t.Value.Size);
            Pal.Invariant(Pal.Implies(going == 0, answer == SpecTree.HasKey(t.Value, key)));
            // Still descending means nothing has been found yet, which is what lets the
            // branch that runs off the bottom stop without touching `answer`.
            Pal.Invariant(Pal.Implies(going == 1, !answer));
            Pal.Decreases(Descent.Sub(t.Value, key, steps).Size + going);

            DescentProof.AtEnd(at, key, steps, t);
            if (at == null)
            {
                going = 0;
            }
            else
            {
                DescentProof.Open(at, at, Descent.Sub(t.Value, key, steps));
                int here = at.key;
                T payload = at.value;
                Knot<T>? lo = at.left;
                Knot<T>? hi = at.right;
                if (here > key)
                {
                    DescentProof.Left(root, at, at, payload, lo, hi, key, steps, t);
                    steps = steps + 1;
                    at = lo;
                }
                else if (here < key)
                {
                    DescentProof.Right(root, at, at, payload, lo, hi, key, steps, t);
                    steps = steps + 1;
                    at = hi;
                }
                else
                {
                    DescentProof.Found(at, at, payload, lo, hi, key, steps, payload, t);
                    answer = true;
                    going = 0;
                }
            }
        }
        DescentProof.Close(root, at, key, steps, t);
        return answer;
    }
}
