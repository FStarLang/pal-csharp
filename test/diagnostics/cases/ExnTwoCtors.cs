// EXPECT: PALCS0612
// One constructor becomes the function that builds the payload; two would need overload
// resolution the translation does not do (R19.1).
using System;

public sealed class Twice : Exception
{
    public int Code { get; }
    public Twice() { Code = 0; }
    public Twice(int code) { Code = code; }
}
