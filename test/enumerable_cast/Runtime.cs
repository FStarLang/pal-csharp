using System;

// No proof annotations: this is run by the stock CLR with PAL undefined.
public static class Runtime
{
    public static int Main()
    {
        bool successful = EnumerableCast.Successful();
        bool failed = EnumerableCast.Failed();
        Console.WriteLine($"successful={successful}; failed={failed}");
        return successful && !failed ? 0 : 1;
    }
}
