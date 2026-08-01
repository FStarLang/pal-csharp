using PalLang;

namespace PalCSharp.Tests;

/// <summary>
/// Insertion sort with the sortedness postcondition (plan tier 7.1a).
///
/// The proof is carried entirely by the annotations below. The inner loop holds a
/// value out of the array in `key` and opens a hole at index `j+1`; what makes the
/// final write correct is a four-part invariant describing the two intact runs on
/// either side of the hole and how they relate to each other and to `key`.
/// </summary>
public static class SortedSpec
{
    // Every predicate here is *total*: the index bounds are part of the antecedent
    // rather than a precondition. A partial predicate would need `i <= a.Length` as a
    // loop invariant, and that is false on entry when the array is empty.
    [Spec]
    public static bool Sorted(Seq<int> s, SpecInt lo, SpecInt hi) =>
        Pal.Forall((int i, int j) => Pal.Implies(
            0 <= i && lo <= i && i < j && j < hi && j < s.Length, s[i] <= s[j]));

    /// <summary>Everything in `[lo, hi)` is strictly greater than `x`.</summary>
    [Spec]
    public static bool AllAbove(Seq<int> s, SpecInt lo, SpecInt hi, SpecInt x) =>
        Pal.Forall((int m) => Pal.Implies(
            0 <= m && lo <= m && m < hi && m < s.Length, x < s[m]));

    /// <summary>Everything in `[lo1, hi1)` is at most everything in `[lo2, hi2)`.</summary>
    [Spec]
    public static bool Dominated(Seq<int> s, SpecInt lo1, SpecInt hi1, SpecInt lo2, SpecInt hi2) =>
        Pal.Forall((int k, int m) => Pal.Implies(
            0 <= k && lo1 <= k && k < hi1 && k < s.Length &&
            0 <= m && lo2 <= m && m < hi2 && m < s.Length, s[k] <= s[m]));
}

/// <summary>
/// The one lemma this proof needs, re-exported from <c>Pulse.Lib.CSharp.Seq</c>. It is a
/// general fact about sequences — moving a cell's neighbour into it while a copy of some
/// value is held aside transposes two cells of the virtual array that includes the held
/// value — and says nothing about sorting.
/// </summary>
public static class SeqLemmas
{
    [Lemma]
    [Requires("0 <= j && j + 1 < Contents(a).Length")]
    [Ensures("IsPermutation(SetAt(Contents(a), j + 1, x), " +
             "SetAt(SetAt(Contents(a), j + 1, Contents(a)[j]), j, x))")]
    [PulseBody("Pulse.Lib.CSharp.Seq.upd_shift_is_permutation $(a) (I32.v $(j)) $(x)")]
    [System.Diagnostics.Conditional("PAL")]
    public static void UpdShiftIsPermutation(int[] a, int j, int x) { }
}

public static class SortingBySortedness
{
    [Ensures("Contents(a).Length == Old(Contents(a)).Length")]
    [Ensures("SortedSpec.Sorted(Contents(a), 0, Contents(a).Length)")]
    [Ensures("IsPermutation(Contents(a), Old(Contents(a)))")]
    public static void InsertionSort(int[] a)
    {
        for (int i = 1; i < a.Length; i++)
        {
            Pal.Invariant(1 <= i);
            Pal.Invariant(Pal.Contents(a).Length == Pal.Old(Pal.Contents(a)).Length);
            Pal.Invariant(SortedSpec.Sorted(Pal.Contents(a), 0, i));
            Pal.Invariant(Pal.IsPermutation(Pal.Contents(a), Pal.Old(Pal.Contents(a))));

            int key = a[i];
            int j = i - 1;
            while (j >= 0 && a[j] > key)
            {
                Pal.Invariant(-1 <= j && j < i);
                Pal.Invariant(i < Pal.Contents(a).Length);
                Pal.Invariant(Pal.Contents(a).Length == Pal.Old(Pal.Contents(a)).Length);
                // The run below the hole is sorted, ...
                Pal.Invariant(SortedSpec.Sorted(Pal.Contents(a), 0, j + 1));
                // ... the run above it is sorted, ...
                Pal.Invariant(SortedSpec.Sorted(Pal.Contents(a), j + 2, i + 1));
                // ... everything above the hole exceeds the value being placed, ...
                Pal.Invariant(SortedSpec.AllAbove(Pal.Contents(a), j + 2, i + 1, key));
                // ... and the two runs are correctly ordered with respect to each other.
                Pal.Invariant(SortedSpec.Dominated(Pal.Contents(a), 0, j + 1, j + 2, i + 1));
                Pal.Invariant(Pal.IsPermutation(
                    Pal.SetAt(Pal.Contents(a), j + 1, key),
                    Pal.Old(Pal.Contents(a))));
                Pal.Decreases(j + 1);

                SeqLemmas.UpdShiftIsPermutation(a, j, key);

                a[j + 1] = a[j];

                // The four parts of the invariant, re-established one at a time for
                // the narrowed hole. Stating them here rather than leaving them to the
                // solver is the whole job of a proof annotation language.
                Pal.Assert(SortedSpec.Sorted(Pal.Contents(a), 0, j));
                Pal.Assert(SortedSpec.Sorted(Pal.Contents(a), j + 1, i + 1));
                Pal.Assert(SortedSpec.AllAbove(Pal.Contents(a), j + 1, i + 1, key));
                Pal.Assert(SortedSpec.Dominated(Pal.Contents(a), 0, j, j + 1, i + 1));

                j--;
            }
            a[j + 1] = key;
        }
    }
}
