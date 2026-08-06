using PalLang;

namespace PalCSharp.Tests;

/// <summary>
/// §15. A recursive class that is <em>parameterised by a type</em>: the M9 counterpart of
/// <c>test/linked_list</c>'s <c>Node</c>.
///
/// <para>Every line below is the monomorphic file with <c>int</c> replaced by <c>T</c> and
/// <c>SpecInt</c> by <c>T</c>. That is the whole content of §15 as a claim about the
/// surface: a generic recursive class is written exactly as a concrete one, and the
/// translation carries the parameter through as binders (R15.1) and applications
/// (R15.3) and changes nothing else.</para>
///
/// <para>R15.5 is visible in the <c>[Model]</c> member. <c>value</c> has type <c>T</c> and
/// its model has type <c>T</c>: §6's conversion exists only where the C# type and its
/// model type differ, and for an unconstrained type parameter they cannot differ, because
/// there is nothing to convert to.</para>
/// </summary>
public sealed class Cell<T>
{
    internal T value;

    /// <summary>
    /// R15.4. The recursive occurrence is at the declaring parameter — a
    /// <c>Cell&lt;T&gt;</c> holds a <c>Cell&lt;T&gt;?</c>, never a <c>Cell&lt;U&gt;?</c>.
    /// C# admits nothing else here without naming a different type, and naming one is what
    /// PALCS0582 refuses.
    /// </summary>
    internal Cell<T>? next;

    [Model]
    private SpecList<T> Items => SpecList.Cons(value, next!.Items);

    /// <summary>R3.10b. How a client names the whole model.</summary>
    [Spec]
    public SpecList<T> Elements => Items;

    /// <summary>
    /// R10.6a through R15.1: the constructor is a function of <c>T</c> as well as of its
    /// arguments, and the binder comes from the class rather than from the method.
    /// </summary>
    [Ensures("@this.Elements == SpecList.Cons(v, n.Elements)")]
    public Cell(T v, Cell<T>? n)
    {
        value = v;
        next = n;
    }
}
