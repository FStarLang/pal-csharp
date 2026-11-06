// EXPECT: PALCS0701
// R27.3. A region's shape is a binary tree, read off the class's two nullable fields of its
// own type. A list node has one, so the region cannot say which pointers are its edges.
using PalLang;

[Region]
public sealed class ListNode
{
    internal int Key;
    internal ListNode? Next;
}
