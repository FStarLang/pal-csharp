// EXPECT: PALCS0592
// R18.1. `ReferenceEquals` is declared in the BCL, not here. The callee walk fell through
// to R2.1's name mangling and emitted a call into `Func_Object_ReferenceEquals`, a module
// that is never generated: exactly the unresolvable reference R18.2's lint detects.
using System;
using PalLang;

public static class Ident
{
    public static bool Same(int[] a, int[] b)
    {
        return ReferenceEquals(a, b);
    }
}
