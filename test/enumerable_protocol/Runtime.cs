using System;
public static class Runtime
{
    public static int Main()
    {
        bool ok = ProtocolClient.Successful() && !ProtocolClient.Failed()
            && ProtocolClient.Generic("payload") && ProtocolClient.StaticBox() && ProtocolClient.StaticStruct()
            && ProtocolClient.ForwardClient() && ProtocolClient.Stale()
            && ProtocolClient.LoopClient(false) && ProtocolClient.LoopClient(true);
        Console.WriteLine($"ordinary/boxed enumeration, disposal, casts, forwarding, stale-version exception: {ok}");
        return ok ? 0 : 1;
    }
}
