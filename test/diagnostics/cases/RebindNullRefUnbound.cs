// EXPECT: PALCS0750
// R30.1. A `ref` local declared null is used on a path where it was never bound.
using System.Runtime.CompilerServices;
using PalLang;

[Spec]
public struct TableModel { public SpecInt N; }

public sealed class Table
{
    private int[] _heads = new int[1];

    [Model] private TableModel Model => new TableModel { N = _heads.Length };

    public void Add(int h, bool bind)
    {
        ref int head = ref Unsafe.NullRef<int>();
        if (bind)
        {
            head = ref _heads[0];
        }
        head = 1;
    }
}
