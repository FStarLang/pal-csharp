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
    public static Seq<T> Splice<T>(Seq<T> parent, SpecInt from, SpecInt to, Seq<T> window) => throw Ghost();

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

    /// <summary>
    /// In a postcondition, the returned value. In the invariant of a loop that contains a
    /// <c>return</c>, the value that <c>return</c> stored (R24.14).
    /// </summary>
    public static T Result<T>() => throw Ghost();

    /// <summary>
    /// In the invariant of a loop that contains a <c>return</c>: whether that <c>return</c>
    /// has run, so the loop is exiting to return <see cref="Result{T}"/> (R24.14, R26.2).
    /// </summary>
    public static bool Returned() => throw Ghost();

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

    /// <summary>
    /// R20.4. The contents of a list. A list is translated as the array it is a view of,
    /// so this is the same sequence <see cref="Contents{T}(T[])"/> denotes.
    /// </summary>
    public static Seq<T> Contents<T>(System.Collections.Generic.IList<T> list) => throw Ghost();

    /// <summary>
    /// R20.5. In a loop invariant of a <c>foreach</c>, the position of the element
    /// <paramref name="element"/> -- the loop's iteration variable -- in the collection:
    /// how many elements the loop has already finished with. It is the counter the
    /// translation of the <c>foreach</c> runs on, which C# gives no name.
    /// </summary>
    public static int Index<T>(T element) => throw Ghost();

    /// <summary>Whether two ghost sequences are permutations of one another.</summary>
    public static bool IsPermutation<T>(Seq<T> left, Seq<T> right) => throw Ghost();

    /// <summary>The ghost sequence <paramref name="s"/> with index <paramref name="index"/> replaced.</summary>
    public static Seq<T> SetAt<T>(Seq<T> s, int index, T value) => throw Ghost();

    /// <summary>The ghost subsequence <c>[from, to)</c>.</summary>
    public static Seq<T> Slice<T>(Seq<T> s, SpecInt from, SpecInt to) => throw Ghost();

    /// <summary>R22.16. <paramref name="s"/> with <paramref name="value"/> appended, F*'s <c>Seq.snoc</c>.</summary>
    public static Seq<T> Snoc<T>(Seq<T> s, T value) => throw Ghost();

    /// <summary>R22.16. Concatenation, F*'s <c>Seq.append</c>.</summary>
    public static Seq<T> Concat<T>(Seq<T> left, Seq<T> right) => throw Ghost();

    /// <summary>R22.16. The empty sequence, F*'s <c>Seq.empty</c>.</summary>
    public static Seq<T> EmptySeq<T>() => throw Ghost();

    /// <summary>
    /// R22.25. <c>EqualityComparer&lt;T&gt;.Default.Equals(x, y)</c>: the equality every
    /// collection without a comparer of its own uses. Nothing is known of it.
    /// </summary>
    public static bool DefaultEquals<T>(T x, T y) => throw Ghost();

    /// <summary>
    /// R22.25. The first position of <paramref name="s"/> whose element
    /// <see cref="DefaultEquals{T}"/> calls equal to <paramref name="value"/>, or -1.
    /// </summary>
    public static SpecInt IndexOf<T>(Seq<T> s, T value) => throw Ghost();

    /// <summary>R22.25. The last such position, or -1.</summary>
    public static SpecInt LastIndexOf<T>(Seq<T> s, T value) => throw Ghost();

    /// <summary>
    /// R22.25. <c>Array.IndexOf(s, value, start, count)</c>: the first such position in
    /// <c>[start, start + count)</c>, or -1.
    /// </summary>
    public static SpecInt IndexOf<T>(Seq<T> s, T value, SpecInt start, SpecInt count) => throw Ghost();

    /// <summary>
    /// R22.25. <c>Array.LastIndexOf(s, value, index, count)</c>: the last such position in
    /// <c>[index - count + 1, index]</c>, or -1.
    /// </summary>
    public static SpecInt LastIndexOf<T>(Seq<T> s, T value, SpecInt index, SpecInt count) => throw Ghost();

    /// <summary>R22.25. <paramref name="s"/> back to front.</summary>
    public static Seq<T> Reverse<T>(Seq<T> s) => throw Ghost();

    /// <summary>
    /// R26.3. The first position of <paramref name="s"/> whose element <paramref name="match"/>
    /// holds of, or -1. A delegate is a pure function in a contract (R26.1): <c>match(x)</c>.
    /// </summary>
    public static SpecInt FindIndex<T>(Seq<T> s, Predicate<T> match) => throw Ghost();

    /// <summary>R26.3. The first such position in <c>[start, start + count)</c>, or -1.</summary>
    public static SpecInt FindIndex<T>(Seq<T> s, Predicate<T> match, SpecInt start, SpecInt count) => throw Ghost();

    /// <summary>R26.3. The last such position, or -1.</summary>
    public static SpecInt FindLastIndex<T>(Seq<T> s, Predicate<T> match) => throw Ghost();

    /// <summary>R26.3. The last such position in <c>[index - count + 1, index]</c>, or -1.</summary>
    public static SpecInt FindLastIndex<T>(Seq<T> s, Predicate<T> match, SpecInt index, SpecInt count) => throw Ghost();

    /// <summary>R26.3. Whether <paramref name="match"/> holds of every element.</summary>
    public static bool TrueForAll<T>(Seq<T> s, Predicate<T> match) => throw Ghost();

    /// <summary>R26.3. The elements <paramref name="match"/> holds of, in order.</summary>
    public static Seq<T> FindAll<T>(Seq<T> s, Predicate<T> match) => throw Ghost();

    /// <summary>R26.3. The elements <paramref name="match"/> does not hold of, in order.</summary>
    public static Seq<T> RemoveAll<T>(Seq<T> s, Predicate<T> match) => throw Ghost();

    /// <summary>R26.3. <paramref name="converter"/> applied to each element.</summary>
    public static Seq<TOutput> ConvertAll<T, TOutput>(Seq<T> s, Converter<T, TOutput> converter) => throw Ghost();

    /// <summary>R26.7. Whether <paramref name="b"/> is <paramref name="a"/> reordered.</summary>
    public static bool Permutation<T>(Seq<T> a, Seq<T> b) => throw Ghost();

    /// <summary>
    /// R26.7. Whether <paramref name="after"/> is <paramref name="before"/> with
    /// <c>[index, index + count)</c> sorted by <paramref name="comparer"/>: a permutation
    /// of that range, sorted, and everything outside it unchanged.
    /// </summary>
    public static bool SortedRange<T>(Seq<T> before, Seq<T> after, SpecInt index, SpecInt count,
        System.Collections.Generic.IComparer<T>? comparer) => throw Ghost();

    /// <summary>
    /// R26.10. Whether <paramref name="s"/> is a 4-ary min-heap of <c>(element, priority)</c>
    /// nodes: every node's priority, by <c>comparer ?? Comparer&lt;TP&gt;.Default</c>, is at
    /// least that of its parent, node <c>i</c>'s parent being <c>(i - 1) / 4</c>.
    /// </summary>
    public static bool IsHeap<TE, TP>(Seq<(TE, TP)> s, System.Collections.Generic.IComparer<TP>? comparer) => throw Ghost();

    /// <summary>R26.10. Whether no node of <paramref name="s"/> has a priority below <paramref name="x"/>'s.</summary>
    public static bool HeapMin<TE, TP>(Seq<(TE, TP)> s, (TE, TP) x, System.Collections.Generic.IComparer<TP>? comparer) => throw Ghost();

    /// <summary>
    /// R26.10. A sift-up loop: <paramref name="x"/> is on its way up to the hole
    /// <paramref name="h"/> of <c>s[0, n)</c>, every edge not touching the hole is in order,
    /// and <c>s[0, n)</c> with <paramref name="x"/> in the hole is <paramref name="t"/> reordered.
    /// </summary>
    public static bool HeapUp<TE, TP>(Seq<(TE, TP)> s, SpecInt n, SpecInt h, (TE, TP) x,
        System.Collections.Generic.IComparer<TP>? comparer, Seq<(TE, TP)> t) => throw Ghost();

    /// <summary>R26.10. A sift-down loop, as <see cref="HeapUp"/> with <paramref name="x"/> on its way down.</summary>
    public static bool HeapDown<TE, TP>(Seq<(TE, TP)> s, SpecInt n, SpecInt h, (TE, TP) x,
        System.Collections.Generic.IComparer<TP>? comparer, Seq<(TE, TP)> t) => throw Ghost();

    /// <summary>R26.10. Whether a sift-up may stop: <paramref name="h"/> is the root, or <paramref name="x"/>'s priority is not below its parent's in <paramref name="s"/>.</summary>
    public static bool HeapUpStop<TE, TP>(Seq<(TE, TP)> s, SpecInt h, (TE, TP) x,
        System.Collections.Generic.IComparer<TP>? comparer) => throw Ghost();

    /// <summary>
    /// R26.10. Whether a sift-down may stop: <paramref name="h"/> has no child in
    /// <c>s[0, n)</c>, or <c>s[m]</c>, a least of its children, is not below <paramref name="x"/>.
    /// </summary>
    public static bool HeapDownStop<TE, TP>(Seq<(TE, TP)> s, SpecInt n, SpecInt h, (TE, TP) x, SpecInt m,
        System.Collections.Generic.IComparer<TP>? comparer) => throw Ghost();

    /// <summary>R26.10. Whether <c>s[m]</c> has a least priority of <c>s[first, i)</c>.</summary>
    public static bool HeapMinChild<TE, TP>(Seq<(TE, TP)> s, SpecInt first, SpecInt i, SpecInt m,
        System.Collections.Generic.IComparer<TP>? comparer) => throw Ghost();

    /// <summary>
    /// R26.10. In a loop invariant: whether a <c>break</c> out of this loop has been taken.
    /// The loop exits as soon as it is, so the invariant may say what held when it was.
    /// </summary>
    public static bool Broke() => throw Ghost();

    /// <summary>R26.2. In a loop invariant: the value that <c>return</c> returned.</summary>
    public static T ReturnValue<T>() => throw Ghost();

    /// <summary>
    /// The ghost sequence <paramref name="s"/> read starting at <paramref name="offset"/>
    /// and wrapping round: <c>Rotate(s, n)[k] == s[(n + k) % s.Length]</c>. The abstraction
    /// function of anything that stores its elements at a moving origin.
    /// </summary>
    public static Seq<T> Rotate<T>(Seq<T> s, int offset) => throw Ghost();

    /// <summary>
    /// R23.10. The <paramref name="count"/> elements of the circular buffer
    /// <paramref name="s"/> read from <paramref name="start"/>, wrapping round once:
    /// <c>Ring(s, h, n)[k] == s[h + k &lt; s.Length ? h + k : h + k - s.Length]</c>. Meaningful when
    /// <c>0 &lt;= h &lt;= s.Length</c> and <c>0 &lt;= n &lt;= s.Length</c>; empty otherwise.
    /// </summary>
    public static Seq<T> Ring<T>(Seq<T> s, SpecInt start, SpecInt count) => throw Ghost();

    // -- Comparers and sorted sequences (doc/translation.md §25) ---------------

    /// <summary>
    /// R25.6. <c>comparer.Compare(x, y)</c>, up to sign: negative, zero or positive as
    /// <paramref name="x"/> is below, equivalent to, or above <paramref name="y"/>.
    /// </summary>
    public static SpecInt Compare<T>(System.Collections.Generic.IComparer<T> comparer, T x, T y) => throw Ghost();

    /// <summary>R25.4. <paramref name="value"/> is the null reference.</summary>
    public static bool IsNull<T>(T value) => throw Ghost();

    /// <summary>R25.6. Each element of <paramref name="s"/> is at most every later one.</summary>
    public static bool Sorted<T>(System.Collections.Generic.IComparer<T> comparer, Seq<T> s) => throw Ghost();

    /// <summary>R25.6. Each element of <paramref name="s"/> is below every later one.</summary>
    public static bool StrictlySorted<T>(System.Collections.Generic.IComparer<T> comparer, Seq<T> s) => throw Ghost();

    /// <summary>
    /// R25.5. What <c>Array.BinarySearch(s, index, count, value, comparer)</c> returns: the
    /// position of an element equivalent to <paramref name="value"/>, or the complement of
    /// where it would go.
    /// </summary>
    public static SpecInt BinarySearch<T>(System.Collections.Generic.IComparer<T> comparer, Seq<T> s,
        SpecInt index, SpecInt count, T value) => throw Ghost();

    /// <summary>
    /// R25.6. The number of elements of <paramref name="s"/> below <paramref name="value"/>:
    /// where it goes in a sorted <paramref name="s"/>.
    /// </summary>
    public static SpecInt LowerBound<T>(System.Collections.Generic.IComparer<T> comparer, Seq<T> s, T value) => throw Ghost();

    /// <summary>
    /// R25.6. In a strictly sorted <paramref name="s"/>, the position of the element
    /// equivalent to <paramref name="value"/>, or -1: <c>LowerBound</c> when what is there
    /// compares equal.
    /// </summary>
    public static SpecInt KeyIndex<T>(System.Collections.Generic.IComparer<T> comparer, Seq<T> s, T value) => throw Ghost();

    // -- Separation-logic propositions -------------------------------------

    /// <summary>The points-to resource for a location, Pulse's <c>pts_to</c>.</summary>
    /// <summary>
    /// R27.7. The tree a reference to a <c>[Region]</c> object reaches through its two child
    /// fields, each node seen through the class's <c>[Model]</c> view <typeparamref name="TV"/>.
    /// Read in the region the enclosing method holds.
    /// </summary>
    public static SpecTree<TV> Tree<TV>(object? node) => throw Ghost();

    /// <summary>
    /// R27.7. The reference reaches only objects of the region the enclosing method holds, and
    /// every path from it ends in <c>null</c>: the region's well-formedness at that pointer.
    /// </summary>
    public static bool WellFormed(object? node) => throw Ghost();

    /// <summary>
    /// R27.13. The reference is a cell of the region the enclosing method holds.
    /// </summary>
    public static bool InRegion(object? node) => throw Ghost();

    /// <summary>
    /// R27.16. The reference is well-formed in the region the enclosing method holds, and the
    /// tree it reaches holds no object twice.
    /// </summary>
    public static bool Unshared(object? node) => throw Ghost();

    /// <summary>
    /// R27.16. In a postcondition: every object outside the tree <paramref name="before"/>
    /// reached on entry is as it was, and the tree <paramref name="after"/> reaches now is
    /// made of objects of that tree and of objects allocated since.
    /// </summary>
    public static bool Reshaped(object? before, object? after) => throw Ghost();

    /// <summary>
    /// R27.18. The first child link (the left child) of a <c>[Region]</c> object in the region
    /// the enclosing method holds, or <c>null</c> if the object is not there.
    /// </summary>
    public static T? LeftOf<T>(T? node) where T : class => throw Ghost();

    /// <summary>R27.18. The second child link (the right child), as <see cref="LeftOf"/>.</summary>
    public static T? RightOf<T>(T? node) where T : class => throw Ghost();

    public static SlProp PtsTo<T>(T location, T value) => throw Ghost();

    /// <summary>Lift a pure proposition into a resource, Pulse's <c>pure</c>.</summary>
    public static SlProp Pure(bool predicate) => throw Ghost();

    /// <summary>An existentially quantified resource, Pulse's <c>exists*</c>.</summary>
    public static SlProp ExistsProp<T>(Func<T, SlProp> body) => throw Ghost();
}
