// EXPECT: PALCS0611
// An exception carries an immutable F* value, so a settable property has no translation
// (R19.1).
using System;

public sealed class Settable : Exception
{
    public int Code { get; set; }
}
