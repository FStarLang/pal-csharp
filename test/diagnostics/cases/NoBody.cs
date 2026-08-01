// EXPECT: PALCS0502
// A declaration with a contract but no proof. C# permits it (an unimplemented partial
// method); pal-csharp must not quietly emit a contract with nothing behind it.
using PalLang;

public static partial class NoBody
{
    [Lemma]
    [Ensures("1 == 1")]
    static partial void Unproved(int x);
}
