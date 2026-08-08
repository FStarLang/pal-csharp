// EXPECT: PALCS0591
// R18.1. A property with a body is a method that happens to be spelled like a field, and
// §9.5 translates only the auto-property, whose backing field is state the model can name.
// A computed property has no field, so the collector matched nothing and — before R18.1 —
// dropped it, verifying a class whose most visible member did not exist.
using PalLang;

public sealed class Rect
{
    private int w;

    [Model]
    private SpecInt TheW => w;

    public Rect(int width)
    {
        Pal.Requires(width > 0);
        this.w = width;
    }

    public int Doubled => w + w;
}
