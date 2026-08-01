using PalLang;

namespace PalCSharp.Probe;

/// <summary>
/// The source of truth for the library-adequacy probe in this directory.
///
/// `Func_InsertionSort.fst` and `Let_Sorted.fst` were produced by hand-executing
/// `doc/translation.md` on this file, rule by rule, before any emitter existed.
/// Each annotation below is load-bearing: removing it makes the derived Pulse
/// fail to verify. That is the point — the proof burden is carried by the
/// annotations and by `Pulse.Lib.CSharp.*`, never by the translator.
/// </summary>
public static class Sorting
{
    [Spec]
    [Requires("0 <= lo && lo <= hi && hi <= a.Length")]
    public static bool Sorted(int[] a, int lo, int hi) =>
        Pal.Forall((int i, int j) =>
            Pal.Implies(lo <= i && i < j && j < hi, a[i] <= a[j]));

    [Ensures("Contents(a).Length == Old(Contents(a)).Length")]
    [Ensures("IsPermutation(Contents(a), Old(Contents(a)))")]
    public static void InsertionSort(int[] a)
    {
        for (int i = 1; i < a.Length; i++)
        {
            // Note `1 <= i` and *not* `1 <= i && i <= a.Length`: the latter is
            // false on entry when `a` is empty. The probe caught that.
            Pal.Invariant(1 <= i);
            Pal.Invariant(Pal.Contents(a).Length == Pal.Old(Pal.Contents(a)).Length);
            Pal.Invariant(Pal.IsPermutation(Pal.Contents(a), Pal.Old(Pal.Contents(a))));

            int key = a[i];
            int j = i - 1;
            while (j >= 0 && a[j] > key)
            {
                Pal.Invariant(-1 <= j && j < i);
                Pal.Invariant(i < Pal.Contents(a).Length);
                Pal.Invariant(Pal.Contents(a).Length == Pal.Old(Pal.Contents(a)).Length);
                Pal.Invariant(Pal.IsPermutation(
                    Pal.SetAt(Pal.Contents(a), j + 1, key),
                    Pal.Old(Pal.Contents(a))));
                Pal.Decreases(j + 1);

                PalSeq.UpdShiftIsPermutation(a, j, key);

                a[j + 1] = a[j];
                j--;
            }
            a[j + 1] = key;
        }
    }
}

/// <summary>
/// Lemmas re-exported from <c>Pulse.Lib.CSharp.Seq</c>. Every one is a
/// general-purpose fact about sequences; none mentions sorting.
/// </summary>
public static class PalSeq
{
    /// <summary>
    /// Moving a cell's neighbour into it, while a copy of some value is held in
    /// a local, transposes two cells of the "virtual" array that includes the
    /// local — and a transposition is a permutation.
    /// </summary>
    [Lemma]
    [Requires("0 <= j && j + 1 < Contents(a).Length")]
    [Ensures("IsPermutation(SetAt(Contents(a), j + 1, x), " +
             "SetAt(SetAt(Contents(a), j + 1, Contents(a)[j]), j, x))")]
    [PulseBody("Pulse.Lib.CSharp.Seq.upd_shift_is_permutation $(a) (Int32.v $(j)) $(x)")]
    [System.Diagnostics.Conditional("PAL")]
    public static void UpdShiftIsPermutation(int[] a, int j, int x) { }
}
