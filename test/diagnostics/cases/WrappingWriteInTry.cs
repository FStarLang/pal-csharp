// EXPECT: PALCS0802
// R32.12. A call that writes the wrapped struct is written back to the field after it
// returns; inside a `try` a raise would skip that write-back, so it is refused there.
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
        public void Step() { _seen = 1; }
    }

    public struct Holder
    {
        private Cursor _inner;
        private readonly int _kind;

        [Ensures("true")]
        public int Advance()
        {
            int r = 0;
            try
            {
                _inner.Step();
            }
            catch (System.InvalidOperationException)
            {
                r = 1;
            }
            return r;
        }
    }
}
