// EXPECT: PALCS0734
// R28.7. A borrowing struct shares the object it borrows: its members are read-only
// members of the object's class, so writing a field of the object is refused.
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
        public void Bump()
        {
            _box._n = _seen;
            _seen++;
        }
    }
}
