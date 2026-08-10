// EXPECT: PALCS0579
// The same for `[Spec]` functions, where the stakes are higher than for a method. R5.9's
// `IsRecursive`/`MentionsSelf` pair asks whether a definition mentions *itself*, so a
// mutually recursive pair is neither marked recursive nor asked for a measure — and an
// unfounded pair of definitions in a logic is not a stuck proof but an inconsistent one.
// What saves it today is that F* never gets far enough to accept them; the refusal
// belongs here, where it can say so.
using PalLang;

public static class MutualSpecs
{
    [Spec]
    public static SpecInt Even(SpecInt n) => n == 0 ? 1 : MutualSpecs.Odd(n - 1);

    [Spec]
    public static SpecInt Odd(SpecInt n) => n == 0 ? 0 : MutualSpecs.Even(n - 1);
}
