using PalLang;

namespace PalCSharp.Tests;

/// <summary>
/// The root of a hierarchy (doc/translation.md §9). An abstract class owns a vtable and
/// no representation (R9.2): there are no fields here, and the <c>[Model]</c> member
/// declares only the model's <em>type</em> — each subclass supplies the value.
/// </summary>
public abstract class Shape
{
    /// <summary>
    /// The model shared by the whole hierarchy: a shape is known by its area. A subclass
    /// may model more than this (a <c>Circle</c> knows its radius), but this is what a
    /// client holding a <c>Shape</c> gets to talk about.
    /// </summary>
    [Refine("Result >= 0")]
    [Model]
    protected abstract SpecInt Area { get; }

    /// <summary>An observation (R3.9c), so that a client outside the class can name the model.</summary>
    [Spec]
    public SpecInt TheArea => Area;

    /// <summary>
    /// A virtual method: one vtable slot (R9.9), and the only place its contract is
    /// written (R9.7). <c>[Frac]</c> says the receiver is observed rather than owned, so a
    /// <c>Shape</c> held at any fraction may be measured and two aliases may measure it at
    /// once. R4.11b derives that from the write set for a method with a body; this one has
    /// none, so it says so.
    /// </summary>
    [Frac("p")]
    [Requires("@this.TheArea <= 2147483647")]
    [Ensures("Result == @this.TheArea")]
    public abstract int GetArea();

    /// <summary>
    /// A mutating virtual method. Doubling every linear dimension quadruples the area.
    /// <para>
    /// The precondition is the interesting one: it is stated at the <em>base</em> model,
    /// and R9.7 makes it the contract every subclass must implement against. It has to be
    /// strong enough for all of them — <c>4 * Area</c> representable bounds a square's side
    /// only because a square's area is the square of its side. A model that did not bound
    /// its own representation this way would need a stronger clause here, and that is the
    /// user's problem to fix, never the translator's.
    /// </para>
    /// </summary>
    [Requires("4 * @this.TheArea <= 2147483647")]
    [Ensures("@this.TheArea == 4 * Old(@this.TheArea)")]
    public abstract void Double();
}
