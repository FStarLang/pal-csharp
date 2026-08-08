using PalLang;

namespace PalCSharp.Tests;

/// <summary>
/// The model of a quadrilateral: its bounding box (R3.9a — a <c>[Spec]</c> struct, so a
/// client can name the two dimensions separately).
/// </summary>
/// <remarks>
/// A bounding box rather than the obvious <c>{ Area, Perimeter }</c>, and the reason is a
/// rule about hierarchies rather than about this example. <c>Shape.Double</c>'s
/// precondition is <c>4 * Area</c> representable, and that is all a subclass gets to
/// assume; from it <c>2*W</c> and <c>2*H</c> are representable whenever both are at least
/// one, because <c>2*W &lt;= 4*W*H</c>. A perimeter admits no such argument — a 1-by-n
/// rectangle has perimeter about twice its area — so a virtual method's precondition,
/// written at the base model, must be strong enough for every subclass's model, and
/// choosing model quantities bounded by the base model's is how a user arranges that.
/// </remarks>
[Spec]
[Refine("Width >= 1")]
[Refine("Height >= 1")]
public struct Box
{
    public SpecInt Width;
    public SpecInt Height;
}

/// <summary>
/// An <em>intermediate</em> class (doc/translation.md R9.18): abstract, with an abstract
/// base of its own. It is both a subclass and a superclass, so it must be packageable into
/// <c>Shape</c>'s vtable <em>and</em> be a vtable of its own that further subclasses fill.
/// </summary>
public abstract class Quadrilateral : Shape
{
    /// <summary>
    /// This class's own model, still abstract: each concrete subclass supplies the value.
    /// </summary>
    [Model]
    protected abstract Box Bounds { get; }

    /// <summary>
    /// R9.6 one level up. The <c>override</c> of the parent's <c>[Model]</c> member is the
    /// forgetting function, and an intermediate class writes one exactly as a leaf does —
    /// which is the point: an intermediate class is just a class.
    /// </summary>
    protected override SpecInt Area => Bounds.Width * Bounds.Height;

    /// <summary>Observations of the intermediate model, unavailable through a <c>Shape</c>.</summary>
    [Spec]
    public SpecInt TheWidth => Bounds.Width;

    [Spec]
    public SpecInt TheHeight => Bounds.Height;

    /// <summary>
    /// A virtual method of this class's own, with a contract stated over the
    /// <em>quadrilateral</em> model — which a caller holding a <c>Quadrilateral</c> can
    /// discharge and a caller holding a <c>Shape</c> cannot even write.
    /// </summary>
    [Frac("p")]
    [Requires("2 * (@this.TheWidth + @this.TheHeight) <= 2147483647")]
    [Ensures("Result == 2 * (@this.TheWidth + @this.TheHeight)")]
    public abstract int Perimeter();

    /// <summary>
    /// R9.7a at an <em>intermediate</em> class, and with two parameters rather than one.
    /// This is the case that exercises R9.18's forwarder — the third wrapper — carrying
    /// arguments through, and it takes them in an order the model does not, so a scheme
    /// that had quietly paired binders with model fields rather than with parameters
    /// would show up here.
    /// </summary>
    [Frac("p")]
    [Requires("1 <= a && a <= 100")]
    [Requires("1 <= b && b <= 100")]
    [Requires("a * @this.TheHeight + b * @this.TheWidth <= 2147483647")]
    [Ensures("Result == a * @this.TheHeight + b * @this.TheWidth")]
    public abstract int Weighted(int a, int b);

    /// <summary>
    /// A <em>non-virtual</em> method of the intermediate class whose body calls one of its
    /// own virtual methods. It has no vtable slot and works for every present and future
    /// subclass.
    /// </summary>
    [Frac("p")]
    [Requires("2 * (@this.TheWidth + @this.TheHeight) <= 2147483647")]
    [Ensures("Result == @this.TheWidth + @this.TheHeight")]
    public int SemiPerimeter()
    {
        return Perimeter() / 2;
    }
}
