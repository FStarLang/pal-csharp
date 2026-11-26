using System;
public static class Runtime
{
    public static int Main()
    {
        bool ok = Projected.Successful(true) && Projected.Successful(false)
            && !Projected.Failed(true) && !Projected.Failed(false)
            && Projected.Generic("payload", true) && Projected.Generic("payload", false);
        Console.WriteLine($"generic projected casts and early returns: {ok}");
        return ok ? 0 : 1;
    }
}
