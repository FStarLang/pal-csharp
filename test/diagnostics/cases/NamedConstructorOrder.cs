// EXPECT: PALCS0001
using System.Collections.Generic;

public static class NamedConstructorOrder
{
    public static KeyValuePair<int, int> Wrong() =>
        new KeyValuePair<int, int>(value: 2, key: 1);
}
