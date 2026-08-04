using PalLang;

namespace PalCSharp.Tests;

/// <summary>
/// §10. A recursive class: one whose representation contains a reference of its own type.
///
/// <para>Everything that makes this hard is in the ownership predicate. A flat class owns
/// one record; this one owns a record <em>and</em> whatever the record's <c>next</c> field
/// points at, and there is no bound on how far that goes. So the predicate has to be an
/// induction — and the thing §10 observes is that the user has already written the
/// induction, in the one member a class with a model owes anyway.</para>
///
/// <para>The <c>[Model]</c> member below says what a <c>Node</c> denotes as a function of
/// its fields. Read left to right it is a definition of <c>Items</c>. Read right to left it
/// is the ownership predicate: a node whose model is <c>hd :: tl</c> owns a cell whose
/// value is <c>hd</c> and whose <c>next</c> owns <c>tl</c>; a null reference owns nothing
/// and denotes <c>[]</c>. The translator inverts the equation (R10.5). The user writes no
/// <c>slprop</c>, no <c>fold</c>, and none of the six case lemmas.</para>
/// </summary>
public sealed class Node
{
    internal int value;

    /// <summary>
    /// R10.2. <c>Node?</c> — the nullable reference is the whole of the base case. It
    /// becomes F*'s <c>option</c>, so <c>n == null</c> is a <em>pattern</em> rather than a
    /// comparison against a distinguished address, and the empty case of the induction is
    /// reachable by the prover without a single lemma about pointers.
    /// </summary>
    internal Node? next;

    /// <summary>
    /// R10.5. The model, as a constructor application over the fields. This is the only
    /// thing the user writes that they would not have written anyway.
    ///
    /// <para>The <c>!</c> is not a claim that <c>next</c> is non-null — it is the reading
    /// that makes the member <em>total</em>. A null reference denotes the empty list, so
    /// <c>next!.Items</c> is <c>[]</c> when <c>next</c> is null, and the equation holds in
    /// both cases. That totality is what lets the translator read it backwards as an
    /// induction with a base case, and it is why nothing here is ever executed.</para>
    /// </summary>
    [Model]
    private SpecList<SpecInt> Items => SpecList.Cons(value, next!.Items);

    /// <summary>R3.10b. How a client names the whole model.</summary>
    [Spec]
    public SpecList<SpecInt> Elements => Items;

    /// <summary>
    /// R10.6a. Allocation is where a new cell enters the induction, and it needs no new
    /// rule: the argument's invariant is transferred into the field exactly as R3.10b
    /// already transfers a sub-object's, and R10.4's <c>intro_cons</c> is R3.10b's
    /// <c>fold</c>.
    /// </summary>
    [Ensures("@this.Elements == SpecList.Cons(v, n.Elements)")]
    public Node(int v, Node? n)
    {
        value = v;
        next = n;
    }
}
