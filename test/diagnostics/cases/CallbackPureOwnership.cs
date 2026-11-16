// EXPECT: PALCS0708
using System;
using PalLang;

[Plain]
public sealed class CallbackPureCell { public int value; }

public static class CallbackPureOwnership
{
    public static bool Run(CallbackPureCell cell,
        [Callback("SpecInt snapshot", "true", "snapshot")] Func<CallbackPureCell, bool> action) => action(cell);
}
