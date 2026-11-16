// EXPECT: PALCS0708
using System;
using PalLang;

[Plain]
public sealed class CallbackCollisionCell { public int value; }

public static class CallbackSnapshotCollision
{
    public static bool Run(CallbackCollisionCell cell,
        [Callback("SpecInt argument", "true", "argument")] Func<CallbackCollisionCell, bool> action) => action(cell);
}
