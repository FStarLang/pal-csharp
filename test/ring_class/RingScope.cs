using PalLang;

namespace PalCSharp.Tests;

/// <summary>
/// R4.14's scope rule. An object local is dropped where C# says its name goes out of
/// scope, not merely at the end of the method — otherwise a buffer allocated in one arm of
/// an <c>if</c> would be dropped in the other, where its binder does not exist, and the
/// generated Pulse would not even parse.
/// </summary>
public static class RingScopes
{
    /// <summary>The buffer exists only on one path, and is discarded on that path.</summary>
    [Ensures("Result == 1")]
    public static int OnlyOnOneBranch(bool b)
    {
        if (b)
        {
            RingBuffer r = new RingBuffer(2);
            r.Enqueue(5);
            return r.Size();
        }
        return 1;
    }

    /// <summary>Two buffers on two paths, neither visible to the other.</summary>
    [Ensures("Result == 1")]
    public static int OneEach(bool b)
    {
        if (b)
        {
            RingBuffer r = new RingBuffer(2);
            r.Enqueue(7);
            return r.Size();
        }
        else
        {
            RingBuffer q = new RingBuffer(5);
            q.Enqueue(8);
            q.Enqueue(9);
            int dropped = q.Dequeue();
            return q.Size();
        }
    }
}
