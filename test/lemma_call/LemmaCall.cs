using System.Diagnostics;
using PalLang;

namespace PalCSharp.Tests;

/// <summary>
/// Lemmas, and the two ways to call one.
///
/// The headline ergonomic claim of pal-csharp is that a lemma application is an
/// ordinary C# method call: it is type-checked, it renames under refactoring, and
/// `[Conditional("PAL")]` erases the entire call — arguments included — from every
/// build that does not define `PAL`. `Pal.GhostStmt` is the escape hatch for proof
/// steps that have no C# surface at all, with PAL's `$(...)` antiquotation.
/// </summary>
public static class Lemmas
{
    /// <summary>A lemma with a C# body: the proof is the specification itself.</summary>
    [Lemma]
    [Requires("0 <= i && i < s.Length")]
    [Ensures("SetAt(s, i, s[i]) == s")]
    [PulseBody("FStar.Seq.lemma_eq_intro (Seq.upd $(s) (I32.v $(i)) (Seq.index $(s) (I32.v $(i)))) $(s)")]
    [Conditional("PAL")]
    public static void SetAtSelfIsIdentity(Seq<int> s, int i) { }

    /// <summary>The same fact, reached through the reusable library instead.</summary>
    [Lemma]
    [Requires("0 <= i && i < s.Length")]
    [Ensures("IsPermutation(s, s)")]
    [PulseBody("Pulse.Lib.CSharp.Seq.is_permutation_refl $(s)")]
    [Conditional("PAL")]
    public static void PermutationRefl(Seq<int> s, int i) { }
}

public static class LemmaUsers
{
    /// <summary>
    /// Writing back what was just read leaves the array alone. Nothing about that
    /// is automatic: `Seq.upd s i (Seq.index s i) == s` needs extensionality, and
    /// the lemma call below is what supplies it.
    /// </summary>
    [Requires("0 <= i && i < Contents(a).Length")]
    [Ensures("Contents(a) == Old(Contents(a))")]
    public static void Touch(int[] a, int i)
    {
        int v = a[i];

        Lemmas.SetAtSelfIsIdentity(Pal.Contents(a), i);
        Lemmas.PermutationRefl(Pal.Contents(a), i);

        a[i] = v;

        // The raw escape hatch: Pulse text, spliced verbatim, with `$(name)`
        // standing for whatever the translator called `name`.
        Pal.GhostStmt("assert (pure (Seq.length $(a) == Seq.length $(a)))");
    }
}
