// EXPECT: PALCS0759
// REFERENCES: lib
// R36.7. The referenced unit was translated without this subclass of its `Shape`.
using PalLang;

namespace PalCSharp.Tests;

public sealed class Square : Shape
{
    protected override SpecInt Area => 4;
}
