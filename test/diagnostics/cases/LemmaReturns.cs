// EXPECT: PALCS0504
using PalLang;

public static class LemmaReturns
{
    [Lemma]
    [Ensures("return == 1")]
    [PulseBody("()")]
    public static int Bad(int x) => 1;
}
