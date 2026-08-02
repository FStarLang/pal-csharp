using PalLang;

namespace PalCSharp.Tests;

/// <summary>
/// The point of the abstraction, from outside it.
///
/// Nothing here mentions <c>head</c>, <c>count</c> or the wrap — a client cannot, because
/// R3.10a made them private to the invariant. FIFO order is provable from the model alone:
/// <c>Enqueue</c> appends and <c>Dequeue</c> removes the front, so two enqueues and a
/// dequeue return the first value, and the argument is a few lines of sequence indexing
/// rather than a case split on whether the buffer happened to wrap.
/// </summary>
public static class Rings
{
    [Ensures("Result == first")]
    public static int FirstOutIsFirstIn(int first, int second)
    {
        RingBuffer r = new RingBuffer(4);
        r.Enqueue(first);
        r.Enqueue(second);
        return r.Dequeue();
    }

    /// <summary>
    /// R4.14: the buffer is allocated here and never leaves, so it is dropped at the exit
    /// — the object's <c>A.pts_to</c> goes with it, which is why the array had to be owned
    /// rather than passed in.
    /// </summary>
    [Ensures("Result == 1")]
    public static int DepthAfterTwoAndOne()
    {
        RingBuffer r = new RingBuffer(2);
        r.Enqueue(10);
        r.Enqueue(20);
        int ignored = r.Dequeue();
        return r.Size();
    }

    /// <summary>
    /// The wrap is unobservable: filling, draining and refilling a capacity-two buffer
    /// moves the origin twice, and the client's specification does not change.
    /// </summary>
    [Ensures("Result == 7")]
    public static int SurvivesAWrap()
    {
        RingBuffer r = new RingBuffer(2);
        r.Enqueue(1);
        r.Enqueue(2);
        int a = r.Dequeue();
        int b = r.Dequeue();
        r.Enqueue(7);
        return r.Dequeue();
    }
}
