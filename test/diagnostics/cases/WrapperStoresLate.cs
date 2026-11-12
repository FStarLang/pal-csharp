// EXPECT: PALCS0595
// R17.10. A span wrapper is translated as the span it holds, so its constructor must
// end by storing its span parameter in the field and must not read the field before.
using System;
using PalLang;

internal ref struct Shelf
{
    private readonly Span<int> _cells;

    public Shelf(Span<int> cells)
    {
        _cells = cells;
        _cells[0] = 1;
    }

    [Ensures("Result == 1")]
    public static int Probe()
    {
        Span<int> buffer = stackalloc int[4];
        Shelf w = new Shelf(buffer);
        return 1;
    }
}
