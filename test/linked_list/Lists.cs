using PalLang;

namespace PalCSharp.Tests;

/// <summary>
/// §10 clients. Recursive traversal of a recursive class, written as ordinary C#.
///
/// <para>The point of every method here is that the proof steps are placed by the program's
/// own control flow. The <c>if (n == null)</c> a C# author has to write anyway <em>is</em>
/// the case split on the model (R10.7): the translator puts the case lemma before the test,
/// opens the head cell at the top of the <c>else</c> branch and closes it again at the
/// bottom. No ghost statement appears in this file.</para>
/// </summary>
public static class Lists
{
    /// <summary>
    /// R10.7. The shape of every recursive traversal. <c>[Decreases]</c> names the model,
    /// and the sub-model being smaller is a fact the case lemma already hands back, so no
    /// measure arithmetic is needed.
    ///
    /// <para>R4.9 over a recursive invariant. A traversal that only reads is <em>observed</em>
    /// rather than owned, and <c>[Frac]</c> is the same word here as on a flat class — what
    /// changes is that the permission has to travel down the induction, which is what
    /// R10.8's recursive share and gather are for. A caller that itself holds only a share
    /// (an owner whose method is <c>preserves</c>) can then traverse what it owns.</para>
    /// </summary>
    [Requires("n.Elements.Length < 2147483647")]
    [Ensures("Result == n.Elements.Length")]
    [Decreases("n.Elements")]
    public static int Length([Frac("p")] Node? n)
    {
        if (n == null)
        {
            return 0;
        }
        return 1 + Length(n.next);
    }

    /// <summary>R10.6a. Allocation, through the constructor.</summary>
    [Ensures("Result.Elements == SpecList.Cons(v, n.Elements)")]
    public static Node Cons(int v, [Consumes] Node? n)
    {
        return new Node(v, n);
    }

    /// <summary>
    /// R10.6b. Destructive traversal: the last <c>next</c> field in <c>x</c> is overwritten
    /// with <c>y</c>. This is the case a flat, non-inductive class predicate cannot express
    /// at all, and the reason §10 exists.
    ///
    /// <para>It is also where R4.9c earns its keep. <c>Append</c> gives both its arguments
    /// away — the result owns them — so neither invariant may appear in the postcondition,
    /// and the null branch has to <em>consume</em> the empty invariant rather than preserve
    /// it. Both are read off <c>[Consumes]</c>; neither is a special case.</para>
    /// </summary>
    [Ensures("Result.Elements == SpecList.Append(x.Elements, y.Elements)")]
    [Decreases("x.Elements")]
    public static Node? Append([Consumes] Node? x, [Consumes] Node? y)
    {
        if (x == null)
        {
            return y;
        }
        x.next = Append(x.next, y);
        return x;
    }
}
