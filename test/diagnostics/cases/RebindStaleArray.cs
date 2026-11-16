// EXPECT: PALCS0750
// R30.2. An array local copied from its field and re-read after one call, but used after
// a second call that may replace the field again: refused.
using PalLang;

[Spec]
public struct TableModel { public SpecInt N; }

public sealed class Table
{
    private int[] _slots = new int[1];

    [Model] private TableModel Model => new TableModel { N = _slots.Length };

    public void Add()
    {
        int[] slots = _slots;
        Grow();
        slots = _slots;
        Grow();
        slots[0] = 1;
    }

    private void Grow() => _slots = new int[_slots.Length + 1];
}
