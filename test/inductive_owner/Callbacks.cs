using System;
using PalLang;

namespace PalCSharp.Tests;

public static class BorrowedCallbacks
{
    [GhostArg("CellSnapshot Before"), GhostArg("Perm Permission")]
    [Preserves("OwnerSpec.Raw(node, Before, Permission)")]
    [Ensures("Pal.Trace<SpecInt, bool>(action).Length == 1")]
    [Ensures("Pal.Trace<SpecInt, bool>(action)[0].Item1 == OwnerSpec.RawValue(Before)")]
    [Ensures("Pal.Trace<SpecInt, bool>(action)[0].Item2 == Result")]
    public static bool Visit(OwnedCell node,
        [Callback("CellSnapshot snapshot", "OwnerSpec.Raw(argument, snapshot, permission)",
                  "OwnerSpec.RawValue(snapshot)")] Func<OwnedCell, bool> action)
    {
        return action(node);
    }

    [GhostArg("CellSnapshot Before"), GhostArg("Perm Permission")]
    [Preserves("OwnerSpec.Raw(node, Before, Permission)")]
    [Ensures("Result == OwnerSpec.RawValue(Before)")]
    public static int ReadOnce(OwnedCell node)
    {
        int result = 0;
        Visit(node, cell =>
        {
#if PAL
            Pal.Protocol<SpecInt, bool>(trace => trace.Length == 0
                ? result == 0
                : result == trace[trace.Length - 1].Item1);
#endif
            result = cell.Current;
            return true;
        });
        return result;
    }
}
