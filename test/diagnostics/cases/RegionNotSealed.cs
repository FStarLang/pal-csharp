// EXPECT: PALCS0700
// R27.3. A region holds one record type, so a `[Region]` class may not be extended: a
// subclass's objects would be cells of a different type in the same heap.
using PalLang;

[Region]
public class OpenNode
{
    internal int Key;
    internal OpenNode? Left;
    internal OpenNode? Right;
}
