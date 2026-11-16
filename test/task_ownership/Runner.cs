using System;
using System.Linq;
using System.Threading;
using System.Threading.Tasks;

public static class TaskChecks
{
    public static async Task Main()
    {
        if (await Downloads.Nested() != 42) throw new Exception("Scalar result changed.");
        int[] left = [0], right = [0];
        await Downloads.Pair(left, right);
        if (left[0] != 17 || right[0] != 29) throw new Exception("Aliased task lost its update.");

        await Chunked.Both([], []);
        await Chunked.Both(new byte[3], new byte[5]);
        byte[] bound = [0];
        await Chunked.BoundWrite(bound, 11);
        if (bound[0] != 11) throw new Exception("Array binder did not update its buffer.");

        var gates = new[] {
            new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously),
            new TaskCompletionSource(TaskCreationOptions.RunContinuationsAsynchronously)
        };
        int entered = 0;
        Suspension.Wait = () =>
        {
            int n = Interlocked.Increment(ref entered);
            return n <= 2 ? gates[n - 1].Task : Task.CompletedTask;
        };
        byte[] a = new byte[5], b = new byte[9];
        try
        {
            Task both = Chunked.Both(a, b);
            if (entered != 2 || both.IsCompleted || a.Any(x => x != 0) || b.Any(x => x != 0))
                throw new Exception("Both operations must suspend before either gate is released.");
            gates[1].SetResult();
            gates[0].SetResult();
            await both.WaitAsync(TimeSpan.FromSeconds(10));
            if (a.Any(x => x != 3) || b.Any(x => x != 7))
                throw new Exception("Suspended fills did not return the promised contents.");
        }
        finally
        {
            foreach (var gate in gates) gate.TrySetResult();
            Suspension.Wait = () => Task.CompletedTask;
        }
        Console.WriteLine("Task runtime: completed and suspended paths, aliasing, empty buffers, and fan-out OK.");
    }
}
