// EXPECT: PALCS0731
// R28.6. A borrowing struct's members are verified, but a call of one from verified code
// is not translated: what the call passes for the borrowed object is not designed.
using PalLang;

[Spec]
public struct BoxModel { public SpecInt N; }

public sealed class Box
{
    private int _n;

    [Model] private BoxModel Model => new BoxModel { N = _n };

    public Box() { }

    [Ensures("true")]
    public int Peek()
    {
        var c = new Cursor(this);
        return c.Read();
    }

    public struct Cursor
    {
        private readonly Box _box;

        internal Cursor(Box box)
        {
            _box = box;
        }

        [Ensures("true")]
        public int Read() => _box._n;
    }
}
