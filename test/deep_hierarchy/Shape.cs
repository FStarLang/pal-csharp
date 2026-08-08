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

    /// <summary>
    /// A virtual method that <em>both</em> mutates the receiver and returns a value —
    /// <c>GetArea</c> and <c>Double</c> at once. It looks like nothing new, and that is the
    /// point: R9.12b is the rule that a dispatching wrapper binds the slot's result exactly
    /// when the slot has one, and it applies on the mutating path just as on the read-only
    /// one. Before it was stated, the three wrappers R9.10 and R9.18 emit bound the result
    /// only on the read-only path, so this combination emitted a wrapper that declared a
    /// return type and ended in the unit from a <c>fold</c>. That is ill-typed Pulse
    /// produced with no diagnostic (§18), which is why the combination is tested here
    /// rather than left to be discovered.
    /// </summary>
    [Requires("4 * @this.TheArea <= 2147483647")]
    [Ensures("@this.TheArea == 4 * Old(@this.TheArea)")]
    [Ensures("Result == Old(@this.TheArea)")]
    public abstract int DoubleAndReport();
}
