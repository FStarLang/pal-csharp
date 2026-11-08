// EXPECT: PALCS0801
// R32.12. A wrapping struct's members are verified as members of the borrowed owner, but
// its constructor is not: building the wrapped struct would need the owner it borrows.
using PalLang;

[Spec]
public struct BoxModel { public SpecInt N; }

public sealed class Box
{
    private int _n;

    [Model] private BoxModel Model => new BoxModel { N = _n };

    public Box() { }

    public struct Cursor
    {
        private readonly Box _box;
        private int _seen;

        internal Cursor(Box box)
        {
            _box = box;
            _seen = 0;
        }

        [Ensures("true")]
        public int Read() => _box._n;
    }

    public struct Holder
    {
        private Cursor _inner;
        private readonly int _kind;

        [Ensures("true")]
        internal Holder(Cursor inner, int kind)
        {
            _inner = inner;
            _kind = kind;
        }

        [Ensures("true")]
        public int Kind() => _kind;
    }
}
