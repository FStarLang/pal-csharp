using System;

namespace PalLang;

/// <summary>
/// R32.10. In-place writes to one node of a region's tree (<c>node.Item = ...</c> on a node
/// a search found): <c>Pulse.Lib.CSharp.RegionReplace</c>. A write that keeps the node's
/// links changes the tree's in-order keys at the node's position only; the library's lemmas
/// fire on their own when the owner's invariant is re-established. The first type argument
/// of each <see cref="RegionOpAttribute"/> member is the <c>[Region]</c> class.
/// </summary>
public static class SpecRegionWrite
{
    private static Exception Ghost() => new InvalidOperationException(
        "SpecRegionWrite is a specification-only construct and has no runtime meaning.");

    /// <summary><paramref name="x"/> is one of the nodes of the tree <paramref name="root"/> reaches in <paramref name="h"/>.</summary>
    [RegionOp("Pulse.Lib.CSharp.RegionReplace.in_tree")]
    public static bool InTree<K, T>(SpecHeap<K> h, K? root, K? x) where K : class => throw Ghost();
}
