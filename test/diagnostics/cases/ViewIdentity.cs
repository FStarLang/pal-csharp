// EXPECT: PALCS0736
// R29.3. A class that borrows is translated as the record of its fields, so two views of
// the same object are equal in the model; comparing their references is refused.
using PalLang;

[Spec]
public struct BoxModel { public SpecInt N; }

public sealed class Box
{
    private int _n;

    [Model] private BoxModel Model => new BoxModel { N = _n };

    public Box() { }

    [Ensures("true")]
    public bool Same()
    {
        var a = new View(this);
        var b = new View(this);
        return a == b;
    }

    public sealed class View
    {
        internal readonly Box _box;

        [Ensures("ReferenceEquals(@this._box, box)")]
        internal View(Box box) => _box = box;
    }
}
