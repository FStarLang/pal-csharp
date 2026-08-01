// EXPECT: PALCS0500
// A program method cannot return a specification-only type. Before Check existed this
// produced Pulse whose return type did not exist, and the user saw an F* error in
// generated code instead of a message about their C#.
using PalLang;

public static class SpecIntReturn
{
    [Ensures("return > 0")]
    public static SpecInt Bad(int x) => x;
}
