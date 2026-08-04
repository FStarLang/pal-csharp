using PalLang;

namespace PalCSharp.Tests;

/// <summary>
/// §10 over a §11 model type. Every rule that applies here is one §10 already had: the
/// class is recursive because it holds a nullable field of its own type, its ownership
/// predicate is read off its <c>[Model]</c> member, and the <c>if (p == null)</c> in the
/// client is the case analysis.
///
/// <para>What is new is only that the model type came from the user's file rather than
/// from the compiler, and that its constructor has three arguments — two pure and one
/// recursive — which is a shape neither <c>SpecList</c> nor <c>SpecTree</c> has.</para>
/// </summary>
public sealed class Pair
{
    internal int key;
    internal int val;
    internal Pair? next;

    /// <summary>
    /// R10.5 unchanged, at a user's constructor. Read right to left it is the ownership
    /// predicate: a chain whose model is <c>Entry k v tl</c> owns a cell whose key is
    /// <c>k</c> and whose value is <c>v</c>, and whose <c>next</c> owns <c>tl</c>. A null
    /// reference owns nothing and denotes <c>Empty</c>, which is the constructor
    /// <c>[SpecCtor(..., Empty = true)]</c> named.
    /// </summary>
    [Model]
    private SpecAssoc<SpecInt, SpecInt> Entries =>
        SpecAssoc.Entry<SpecInt, SpecInt>(key, val, next!.Entries);

    /// <summary>R3.10b. How a client names the whole model.</summary>
    [Spec]
    public SpecAssoc<SpecInt, SpecInt> Map => Entries;

    [Ensures("@this.Map == SpecAssoc.Entry<SpecInt, SpecInt>(k, v, n.Map)")]
    public Pair(int k, int v, Pair? n)
    {
        key = k;
        val = v;
        next = n;
    }
}
