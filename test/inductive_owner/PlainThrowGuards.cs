using System;
using PalLang;

namespace PalCSharp.Tests;

public static class PlainThrowGuards
{
    [Throws(typeof(ArgumentNullException), "cell == null")]
    [Ensures("Result && cell != null")]
    public static bool Require<T>(CallbackCell<T>? cell)
    {
        if (cell == null)
            throw new ArgumentNullException(nameof(cell));
        return true;
    }

    [Requires("calls < int.MaxValue")]
    [Ensures("Result == cell && calls == Pal.Old(calls) + 1")]
    public static CallbackCell<T>? Observe<T>(CallbackCell<T>? cell, ref int calls)
    {
        calls++;
        return cell;
    }

    [Requires("calls < int.MaxValue && completed < int.MaxValue")]
    [Throws(typeof(ArgumentNullException), "cell == null")]
    [Ensures("Result && cell != null && calls == Pal.Old(calls) + 1 && completed == Pal.Old(completed) + 1")]
    public static bool Effectful<T>(CallbackCell<T>? cell, ref int calls, ref int completed)
    {
        if (Observe(cell, ref calls) == null)
            throw new ArgumentNullException(nameof(cell));
        completed++;
        return true;
    }
}
