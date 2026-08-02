using PalLang;

namespace PalCSharp.Tests;

/// <summary>
/// R3.9a: a <em>spec-only</em> struct. <c>[Spec]</c> on a type means what it means on a
/// method — this exists only in specifications — so, unlike an ordinary translated struct
/// (R3.4, PALCS0511), its fields may be ghost types such as <c>Seq&lt;T&gt;</c>.
///
/// It is here because R3.9 forces it. The model of a bounded container has to expose its
/// capacity as well as its contents, or a caller cannot state "the stack is not full" and
/// <c>Push</c> becomes uncallable; and every built-in spec-only type is atomic, so a
/// product model cannot be written without a way to declare one.
/// </summary>
[Spec]
public struct StackModel
{
    public Seq<int> Elems;
    public SpecInt Capacity;
}

/// <summary>
/// A class that <em>owns</em> its storage — the thing a struct cannot do.
/// <c>test/circular_buffer</c> had to pass its array alongside the struct describing it,
/// because copying a struct with an array field would duplicate ownership (PALCS0511). A
/// class is a heap cell, so R3.10a can put the array's <c>A.pts_to</c> inside the object
/// invariant and the storage becomes genuinely private: a client of <c>Stack</c> never
/// names <c>items</c>, and cannot alias it.
/// </summary>
[Invariant("0 <= top")]
[Invariant("top <= items.Length")]
public sealed class Stack
{
    private int[] items;
    private int top;

    /// <summary>
    /// The abstraction function (R3.9b). It is <em>partial</em>: the slice is well-typed
    /// only once <c>0 &lt;= top &lt;= items.Length</c> is known, which is precisely why the
    /// relation is inlined as a conjunct of the invariant, after the bounds, rather than
    /// factored out as a total function whose refinement every use would have to discharge.
    ///
    /// Inside a class-level clause an array field denotes its <em>contents</em>, exactly as
    /// an array parameter does in a method contract (R4.4): <c>items.Length</c> is the
    /// length of the sequence, and <c>Pal.Contents(items)</c> is that sequence.
    /// </summary>
    [Refine("Result.Elems.Length <= Result.Capacity")]
    [Model]
    private StackModel Model => new StackModel
    {
        Elems = Pal.Slice(Pal.Contents(items), 0, top),
        Capacity = items.Length,
    };

    /// <summary>The observations (R3.9c): pure functions of the model, never of the fields.</summary>
    [Spec]
    public Seq<int> Elems => Model.Elems;

    [Spec]
    public SpecInt Count => Model.Elems.Length;

    [Spec]
    public SpecInt Capacity => Model.Capacity;

    [Requires("0 <= capacity")]
    [Ensures("@this.Count == 0")]
    [Ensures("@this.Capacity == capacity")]
    public Stack(int capacity)
    {
        items = new int[capacity];
        top = 0;
    }

    /// <summary>
    /// The precondition is stated over the model, which is the whole point of R3.9c: a
    /// caller holds the invariant opaquely, so "there is room" has to be computable from
    /// the model alone. The postcondition characterises the new contents element by
    /// element rather than as a sequence equation, so the proof stays inside what SMT
    /// decides.
    /// </summary>
    [Requires("@this.Count < @this.Capacity")]
    [Ensures("@this.Capacity == Old(@this.Capacity)")]
    [Ensures("@this.Count == Old(@this.Count) + 1")]
    [Ensures("@this.Elems[Old(@this.Count)] == v")]
    [Ensures("Forall((int i) => Implies(0 <= i && i < Old(@this.Count), @this.Elems[i] == Old(@this.Elems)[i]))")]
    public void Push(int v)
    {
        items[top] = v;
        top = top + 1;
    }

    /// <summary>
    /// The invariant is transiently false here: after <c>top = top - 1</c> the object no
    /// longer abstracts to the model it came in with. That is exactly why a class
    /// invariant is a conjunct inside the predicate and not a refinement on the
    /// representation (R3.10) — a refinement would have to hold of every intermediate
    /// value, and this one does not.
    /// </summary>
    [Requires("0 < @this.Count")]
    [Ensures("@this.Capacity == Old(@this.Capacity)")]
    [Ensures("@this.Count == Old(@this.Count) - 1")]
    [Ensures("Result == Old(@this.Elems)[Old(@this.Count) - 1]")]
    [Ensures("Forall((int i) => Implies(0 <= i && i < @this.Count, @this.Elems[i] == Old(@this.Elems)[i]))")]
    public int Pop()
    {
        top = top - 1;
        return items[top];
    }

    [Ensures("Result == @this.Count")]
    public int Size()
    {
        return top;
    }
}
