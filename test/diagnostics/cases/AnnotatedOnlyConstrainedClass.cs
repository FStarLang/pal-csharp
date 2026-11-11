// EXPECT: PALCS0580
using PalLang;

[assembly: TranslateAnnotatedOnly]

public sealed class AnnotatedConstrainedCell<T> where T : struct
{
    [Model]
    private SpecInt State => 0;
}
