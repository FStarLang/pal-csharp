// EXPECT: PALCS0615
// `[Throws]` names an exception class: what is thrown is matched by its class's
// discriminator (R19.3).
using System;
using PalLang;

public static class ThrowsInt
{
    [Throws(typeof(int))]
    public static int F(int x) => x;
}
