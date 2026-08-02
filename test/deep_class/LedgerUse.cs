using PalLang;

namespace PalCSharp.Tests;

/// <summary>
/// Three levels of ownership, from the outside. A client names <c>Data</c> and
/// <c>Count</c>; it never learns that the count is a <c>Cell</c> inside a <c>Cursor</c>
/// inside the <c>Ledger</c>, and it never names <c>slots</c> either.
/// </summary>
public static class LedgerUse
{
    [Ensures("Result == 7")]
    public static int BuildAndRead()
    {
        Ledger l = new Ledger(4);
        l.Append(7);
        return l.Get(0);
    }

    /// <summary>
    /// Two appends compose through the whole hierarchy: the first one's element-by-element
    /// postcondition is what lets the second one's frame carry it out.
    /// </summary>
    [Requires("l.Count + 2 <= l.Capacity")]
    [Ensures("l.Count == Old(l.Count) + 2")]
    [Ensures("l.Data[Old(l.Count)] == x")]
    [Ensures("l.Data[Old(l.Count) + 1] == y")]
    public static void AppendTwo(Ledger l, int x, int y)
    {
        l.Append(x);
        l.Append(y);
    }

    /// <summary>
    /// Separation through three levels: appending to one ledger leaves the other's
    /// contents alone, down to the <c>Cell</c>s.
    /// </summary>
    [Requires("a.Count < a.Capacity")]
    [Ensures("a.Count == Old(a.Count) + 1")]
    [Ensures("b.Count == Old(b.Count)")]
    [Ensures("b.Data == Old(b.Data)")]
    public static void AppendToOne(Ledger a, Ledger b, int v)
    {
        a.Append(v);
    }

    /// <summary>
    /// <c>Size</c> reads through two owned objects and assigns nothing, so R4.11's
    /// call-following read-only test gives it <c>preserves</c> and the caller keeps
    /// everything it knew.
    /// </summary>
    [Ensures("Result == Old(l.Count)")]
    [Ensures("l.Data == Old(l.Data)")]
    public static int MeasureTwice(Ledger l)
    {
        int first = l.Size();
        int second = l.Size();
        return second;
    }
}
