using System;
using PalLang;

[assembly: IncludePulse("UserAcct", """
module UserAcct

/// A rewards model: a balance and a point count. Strictly more than the balance alone.
noeq type acct = { bal: int; pts: int }

let mk (b p: int) : acct = { bal = b; pts = p }
let bal (a: acct) : int = a.bal
let pts (a: acct) : int = a.pts
""")]

[SpecType("UserAcct.acct")]
public readonly struct SpecAcct
{
    private static Exception Ghost() => new InvalidOperationException(
        "SpecAcct is a specification-only construct and has no runtime meaning.");

    [SpecOp("UserAcct.bal")]
    public SpecInt Bal => throw Ghost();

    [SpecOp("UserAcct.pts")]
    public SpecInt Pts => throw Ghost();

    public static bool operator ==(SpecAcct a, SpecAcct b) => throw Ghost();
    public static bool operator !=(SpecAcct a, SpecAcct b) => throw Ghost();
    public override bool Equals(object? obj) => throw Ghost();
    public override int GetHashCode() => throw Ghost();
}

public static class SpecAcctOps
{
    private static Exception Ghost() => new InvalidOperationException(
        "SpecAcctOps is a specification-only construct and has no runtime meaning.");

    [SpecCtor("UserAcct.mk")]
    public static SpecAcct Mk(SpecInt b, SpecInt p) => throw Ghost();
}
