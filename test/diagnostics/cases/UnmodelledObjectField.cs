// EXPECT: PALCS0500
// R3.10b's likeliest first mistake. A class is translated exactly when it declares a
// [Model] — R3.9 makes the model mandatory, so its presence is the same test as "the user
// asked us to translate this". A field whose type is a class *without* one therefore fails
// the type map rather than the ownership rule, and the message has to say which: there is
// nothing wrong with owning an object, only with owning this one.
using PalLang;

public sealed class Untranslated
{
    private int v;

    public int Read()
    {
        return v;
    }
}

public sealed class Holder
{
    private Untranslated inner;
    private int n;

    [Model]
    private SpecInt Model => n;

    [Spec]
    public SpecInt Count => Model;

    [Ensures("@this.Count == 0")]
    public Holder()
    {
        n = 0;
    }
}
