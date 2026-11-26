using System.Collections.Generic;
using PalLang;

// Compile against the translated runtime List reference, not a substitute.
public static class ListMiss
{
    [Ensures("Result")]
    public static bool Run()
    {
        var source = new List<int>();
        source.Add(2);
        source.Add(3);
        source.Add(4);
        source.Add(9);
        bool matched = ObservationClient.Observe(source);
        Pal.Assert(source.Items.Length == 4 &&
            source.Items[0] == 2 && source.Items[1] == 3 &&
            source.Items[2] == 4 && source.Items[3] == 9);
        return !matched && source.Count == 4;
    }
}
