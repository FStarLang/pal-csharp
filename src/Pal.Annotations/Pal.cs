using System;
using System.Diagnostics;

namespace PalLang;

/// <summary>
/// Proof intrinsics for statement positions that attributes cannot reach:
/// loop invariants, assertions, ghost statements, and the spec-only vocabulary
/// (<c>Old</c>, <c>Result</c>, quantifiers, array contents).
/// </summary>
/// <remarks>
/// <para>
/// The <c>void</c>-returning intrinsics are <c>[Conditional("PAL")]</c>: unless
/// <c>PAL</c> is defined, the C# compiler removes the entire call site
/// <em>including argument evaluation</em>, so annotations cost nothing at
/// runtime and cannot change behaviour.
/// </para>
/// <para>
/// The value-returning intrinsics (<c>Old</c>, <c>Result</c>, <c>Forall</c>, …)
/// exist only to be written inside specifications. They cannot be
/// <c>[Conditional]</c> because they return a value, but they only ever appear
/// as arguments to a conditional intrinsic or inside an attribute string, so
/// they are erased along with their enclosing call. Invoking one directly is a
/// programming error and throws.
/// </para>
/// </remarks>
public static class Pal
{
    private const string Cond = "PAL";

    private static Exception Ghost([System.Runtime.CompilerServices.CallerMemberName] string member = "")
        => new InvalidOperationException(
            $"Pal.{member} is a specification-only construct and has no runtime meaning. " +
            "It may only appear inside a specification.");

    // -- Contracts in statement position -----------------------------------

    /// <summary>A precondition, written as the first statements of a method body.</summary>
    [Conditional(Cond)]
    public static void Requires(bool predicate) { }

    /// <summary>A postcondition. Inside a loop body, the condition holding at a <c>break</c>.</summary>
    [Conditional(Cond)]
    public static void Ensures(bool predicate) { }

    /// <summary>A loop invariant. Written as a leading statement of the loop body.</summary>
    [Conditional(Cond)]
    public static void Invariant(bool predicate) { }

    /// <summary>
    /// A loop invariant that *owns* something: the ownership a loop holds at the top of
    /// every iteration. This is what a cursor needs — a loop that walks a data structure
    /// owns a different part of it on each iteration, and a proposition about values
    /// cannot say that. Written exactly like the other form, with an <c>SlProp</c>-valued
    /// <c>[SpecOp]</c> in place of the condition.
    /// </summary>
    [Conditional(Cond)]
    public static void Invariant(SlProp ownership) { }

    /// <summary>A termination measure. Written as a leading statement of the loop body.</summary>
    [Conditional(Cond)]
    public static void Decreases(int measure) { }

    /// <inheritdoc cref="Decreases(int)"/>
    [Conditional(Cond)]
    public static void Decreases(SpecInt measure) { }

    /// <summary>A verification assertion.</summary>
    [Conditional(Cond)]
    public static void Assert(bool predicate) { }

    /// <summary>Assume a predicate without proof. Reported as a diagnostic.</summary>
    [Conditional(Cond)]
    public static void Assume(bool predicate) { }

    // -- Permissions -------------------------------------------------------

    /// <summary>
    /// Halve the permission held on <paramref name="location"/>, an array or an object,
    /// so that it can be observed through two names at once. Pulse never splits a
    /// permission on its own, and no frontend can tell where a split is wanted, so the
    /// split is written here — like every other proof step, by the author.
    /// </summary>
    [Conditional(Cond)]
    public static void Share<T>(T location) { }

    /// <summary>
    /// Recombine the two halves <see cref="Share{T}"/> produced. It is <c>Share</c>'s
    /// exact inverse, so the pair round-trips with nothing in between, and it proves the
    /// two views agreed about what they were observing.
    /// </summary>
    [Conditional(Cond)]
    public static void Gather<T>(T location) { }

    // -- Spans -------------------------------------------------------------

    /// <summary>
    /// Give a borrowed span back to the array or span it was taken from.
    /// </summary>
    /// <remarks>
    /// <para>
    /// Creating a span — <c>a.AsSpan(i, n)</c>, <c>s.Slice(i, n)</c>, <c>s[i..j]</c>, or
    /// the implicit <c>T[]</c> conversion — <em>borrows</em>: the parent's contents can no
    /// longer be read or written through the parent's own name until the borrow ends.
    /// C# says nothing about where it ends, and inferring that is a borrow checker, which
    /// pal-csharp does not have and does not want. So the end of the borrow is written,
    /// once, by the author, exactly like every other proof step.
    /// </para>
    /// <para>
    /// Forgetting it is not unsound, merely unprovable: the parent's ownership is missing
    /// where the postcondition needs it. Writing it too early is equally safe: the span's
    /// own ownership is gone, and the next use of <paramref name="span"/> fails to verify.
    /// </para>
    /// <para>
    /// Afterwards the parent holds <see cref="Splice{T}"/> of what it lent out: the span's
    /// current contents in the window, everything outside it untouched.
    /// </para>
    /// </remarks>
    [Conditional(Cond)]
    public static void Restore<T>(Span<T> span) { }

    /// <inheritdoc cref="Restore{T}(Span{T})"/>
    [Conditional(Cond)]
    public static void Restore<T>(ReadOnlySpan<T> span) { }

    /// <summary>
    /// The contents of a parent after the window <c>[from, to)</c> is given back holding
    /// <paramref name="window"/>: <c>parent</c> outside the window, <paramref name="window"/>
    /// inside it. This is what <see cref="Restore{T}(Span{T})"/> leaves behind.
    /// </summary>
    public static Seq<T> Splice<T>(Seq<T> parent, int from, int to, Seq<T> window) => throw Ghost();

    // -- Escape hatches to raw Pulse ---------------------------------------

    /// <summary>Emit a verbatim Pulse statement, after antiquotation expansion.</summary>
    [Conditional(Cond)]
    public static void GhostStmt(string pulse) { }

    /// <summary>Mark a call as ghost. The call is erased at runtime.</summary>
    [Conditional(Cond)]
    public static void GhostCall(Action call) { }

    /// <summary>A verbatim Pulse expression in a specification position.</summary>
    public static bool InlinePulse(string pulse) => throw Ghost();

    /// <summary>Assert ownership of a local, when inference cannot see it.</summary>
    public static bool Live<T>(T location) => throw Ghost();

    // -- Spec-only vocabulary ----------------------------------------------

    /// <summary>In a postcondition, the value of <paramref name="expression"/> on entry.</summary>
    public static T Old<T>(T expression) => throw Ghost();

    /// <summary>In a postcondition, the returned value.</summary>
    public static T Result<T>() => throw Ghost();

    /// <summary>Logical implication.</summary>
    public static bool Implies(bool antecedent, bool consequent) => throw Ghost();

    /// <summary>Logical equivalence.</summary>
    public static bool Iff(bool left, bool right) => throw Ghost();

    /// <summary>
    /// Specification-level equality (R15.6). C#'s <c>==</c> is not defined on an
    /// unconstrained type parameter — there is no operator to resolve and no
    /// <c>IEquatable</c> to call — so a contract about a value of such a type says
    /// <c>Pal.Same(a, b)</c> instead. It denotes F*'s <c>==</c>, which is the equality
    /// every other spec-position <c>==</c> already denotes; only the C# spelling differs,
    /// and only because C# has no spelling of its own here.
    /// </summary>
    public static bool Same<T>(T left, T right) => throw Ghost();

    public static bool Forall<T1>(Func<T1, bool> body) => throw Ghost();
    public static bool Forall<T1, T2>(Func<T1, T2, bool> body) => throw Ghost();
    public static bool Forall<T1, T2, T3>(Func<T1, T2, T3, bool> body) => throw Ghost();

    public static bool Exists<T1>(Func<T1, bool> body) => throw Ghost();
    public static bool Exists<T1, T2>(Func<T1, T2, bool> body) => throw Ghost();

    /// <summary>The ghost sequence of an array's contents, for use in specifications.</summary>
    public static Seq<T> Contents<T>(T[] array) => throw Ghost();

    /// <inheritdoc cref="Contents{T}(T[])"/>
    public static Seq<T> Contents<T>(Span<T> span) => throw Ghost();

    /// <inheritdoc cref="Contents{T}(T[])"/>
    public static Seq<T> Contents<T>(ReadOnlySpan<T> span) => throw Ghost();

    /// <summary>Whether two ghost sequences are permutations of one another.</summary>
    public static bool IsPermutation<T>(Seq<T> left, Seq<T> right) => throw Ghost();

    /// <summary>The ghost sequence <paramref name="s"/> with index <paramref name="index"/> replaced.</summary>
    public static Seq<T> SetAt<T>(Seq<T> s, int index, T value) => throw Ghost();

    /// <summary>The ghost subsequence <c>[from, to)</c>.</summary>
    public static Seq<T> Slice<T>(Seq<T> s, int from, int to) => throw Ghost();

    /// <summary>
    /// The ghost sequence <paramref name="s"/> read starting at <paramref name="offset"/>
    /// and wrapping round: <c>Rotate(s, n)[k] == s[(n + k) % s.Length]</c>. The abstraction
    /// function of anything that stores its elements at a moving origin.
    /// </summary>
    public static Seq<T> Rotate<T>(Seq<T> s, int offset) => throw Ghost();

    // -- Separation-logic propositions -------------------------------------

    /// <summary>The points-to resource for a location, Pulse's <c>pts_to</c>.</summary>
    public static SlProp PtsTo<T>(T location, T value) => throw Ghost();

    /// <summary>Lift a pure proposition into a resource, Pulse's <c>pure</c>.</summary>
    public static SlProp Pure(bool predicate) => throw Ghost();

    /// <summary>An existentially quantified resource, Pulse's <c>exists*</c>.</summary>
    public static SlProp ExistsProp<T>(Func<T, SlProp> body) => throw Ghost();
}
