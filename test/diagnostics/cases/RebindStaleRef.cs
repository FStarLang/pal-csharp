// EXPECT: PALCS0750
// R30.1. A `ref` local into a field's array is rebound after `Grow` on one path only, so
// on the other it would still name the old array's element: refused.
using System.Runtime.CompilerServices;
using PalLang;

[Spec]
public struct TableModel { public SpecInt N; }

public sealed class Table
{
    private int[] _heads = new int[1];

    [Model] private TableModel Model => new TableModel { N = _heads.Length };

    public void Add(int h, bool grow)
    {
        ref int head = ref HeadRef(h);
        if (grow)
        {
            Grow();
        }
        else
        {
            head = ref HeadRef(h);
        }
        head = 1;
    }

    private void Grow() => _heads = new int[_heads.Length + 1];

    private ref int HeadRef(int h)
    {
        int[] heads = _heads;
        return ref heads[(uint)h % (uint)heads.Length];
    }
}
