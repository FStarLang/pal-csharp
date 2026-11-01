// EXPECT: PALCS0610
// An exception class's payload includes its base's fields, so the base must be one the
// translator can see: System.Exception or an exception class of the program (R19.1).
using System;

public sealed class Wrapped : InvalidOperationException
{
}
