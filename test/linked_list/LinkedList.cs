using PalLang;

namespace PalCSharp.Tests;

/// <summary>
/// R3.10b over a recursive field. A handle class: not itself recursive — nothing inside a
/// <c>LinkedList</c> is a <c>LinkedList</c> — but it owns one nullable <c>Node</c>, and so
/// owns the whole chain hanging off it.
///
/// <para>This is the composition §10 has to survive. The sub-invariant R3.10b puts in the
/// owner's invariant for a field of class type is, for this field, the <em>inductive</em>
/// one at the option (R10.3), and the owner's model is that field's model. Nothing in
/// R3.10b changes; the field's invariant is simply a different slprop.</para>
/// </summary>
public sealed class LinkedList
{
    private Node? head;

    /// <summary>
    /// R10.5's <c>!</c> reading again, and for the same reason: an empty list is a null
    /// <c>head</c>, and it denotes the empty sequence. This member is not an induction —
    /// it names the field's model, exactly as any owner names a sub-object's.
    /// </summary>
    [Model]
    private SpecList<SpecInt> Items => head!.Elements;

    [Spec]
    public SpecList<SpecInt> Elements => Items;

    [Ensures("@this.Elements == SpecList.Empty<SpecInt>()")]
    public LinkedList()
    {
        head = null;
    }

    /// <summary>
    /// The field is read, given away to the constructor (R4.12b) and replaced by what the
    /// constructor built out of it. C# writes that as one assignment.
    /// </summary>
    [Ensures("@this.Elements == SpecList.Cons(v, Old(@this.Elements))")]
    public void Push(int v)
    {
        head = new Node(v, head);
    }

    /// <summary>A read that hands the field to a traversal and gets it back.</summary>
    [Requires("@this.Elements.Length < 2147483647")]
    [Ensures("Result == @this.Elements.Length")]
    [Ensures("@this.Elements == Old(@this.Elements)")]
    public int Count()
    {
        return Lists.Length(head);
    }
}
