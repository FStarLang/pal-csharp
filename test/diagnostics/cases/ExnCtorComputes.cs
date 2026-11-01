// EXPECT: PALCS0613
// An exception constructor is a pure function of its parameters: it may pass them on and
// store them, but not compute with them (R19.1).
using System;

public sealed class Doubled : Exception
{
    public int Code { get; }
    public Doubled(int code) { Code = code * 2; }
}
