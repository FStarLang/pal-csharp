// EXPECT: PALCS0735
// R29.3b. `v ??= new View(this)` is the view only when every write of the cache is such a
// fill; here `Reset` stores something else, so the fill is not recognised and refused.
using PalLang;

[Spec]
public struct BoxModel { public SpecInt N; }

public sealed class Box
{
    private int _n;
    private View? _view;

    [Model] private BoxModel Model => new BoxModel { N = _n };

    public Box() { }

    public void Reset(View v) => _view = v;

    [Ensures("ReferenceEquals(Result._box, @this)")]
    public View Get() => _view ??= new View(this);

    public sealed class View
    {
        internal readonly Box _box;

        [Ensures("ReferenceEquals(@this._box, box)")]
        internal View(Box box) => _box = box;
    }
}
