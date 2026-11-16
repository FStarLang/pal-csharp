using System;
using PalLang;

namespace PalCSharp.Tests;

public sealed class OwnedCallChild
{
    private int value;
    [Model] private SpecInt Model => value;
    [Spec] public SpecInt Value => Model;

    [Ensures("@this.Value == value")]
    public OwnedCallChild(int value) { this.value = value; }

    [Requires("calls == 0")]
    [Throws(typeof(InvalidOperationException), "fail")]
    [Ensures("!fail && Result == @this.Value && calls == 1")]
    public int Read(bool fail, ref int calls)
    {
        calls++;
        if (fail) throw new InvalidOperationException();
        return value;
    }
}

[Spec]
public struct OwnedCallModel
{
    public SpecInt Child;
    public SpecInt Stamp;
}

public sealed class OwnedCallHolder
{
    private OwnedCallChild child;
    private int stamp;
    [Model] private OwnedCallModel Model => new OwnedCallModel { Child = child.Value, Stamp = stamp };
    [Spec] public SpecInt Value => Model.Child;
    [Spec] public SpecInt Stamp => Model.Stamp;

    [Ensures("@this.Value == value && @this.Stamp == stamp")]
    public OwnedCallHolder(int value, int stamp)
    {
        child = new OwnedCallChild(value);
        this.stamp = stamp;
    }

    [Requires("calls == 0")]
    [Throws(typeof(InvalidOperationException), "fail")]
    [Ensures("!fail && Result == @this.Value && calls == 1")]
    [Ensures("@this.Value == Pal.Old(@this.Value) && @this.Stamp == Pal.Old(@this.Stamp)")]
    public int Read(bool fail, ref int calls)
    {
        return child.Read(fail, ref calls);
    }

    [Requires("observations < int.MaxValue")]
    [Ensures("Result == fail && observations == Pal.Old(observations) + 1")]
    public static bool Observe(bool fail, ref int observations)
    {
        observations++;
        return fail;
    }

    [Requires("calls == 0 && observations < int.MaxValue")]
    [Throws(typeof(InvalidOperationException), "fail")]
    [Ensures("!fail && Result == @this.Value && calls == 1 && observations == Pal.Old(observations) + 1")]
    [Ensures("@this.Value == Pal.Old(@this.Value) && @this.Stamp == Pal.Old(@this.Stamp)")]
    public int ReadObserved(bool fail, ref int calls, ref int observations)
    {
        return child.Read(Observe(fail, ref observations), ref calls);
    }

    [Requires("calls == 0")]
    [Ensures("holder.Value == Pal.Old(holder.Value) && holder.Stamp == Pal.Old(holder.Stamp)")]
    [Ensures("unrelated.Value == Pal.Old(unrelated.Value)")]
    [Ensures("Result == holder.Value || Result == 0")]
    public static int Recover(OwnedCallHolder holder, OwnedCallChild unrelated, bool fail, ref int calls)
    {
        int result = 0;
        try
        {
            Pal.Invariant(result == 0 || result == holder.Value);
            result = holder.Read(fail, ref calls);
        }
        catch (InvalidOperationException)
        {
            result = 0;
        }
        return result;
    }
}
