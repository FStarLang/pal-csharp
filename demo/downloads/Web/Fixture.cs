using System.Collections.Concurrent;

namespace AsyncDownloads.Web;

public sealed record Artifact(string Name, int Length, int Seed, int Chunk)
{
    public byte[] Bytes() => Enumerable.Range(0, Length).Select(i => (byte)((i * 17 + Seed) % 256)).ToArray();
}

public static class Fixture
{
    public static readonly Artifact[] Artifacts =
    [
        new("amber.bin", 4096, 19, 137),
        new("blue.bin", 6144, 73, 251)
    ];

    private sealed class Gate
    {
        public readonly TaskCompletionSource Release = new(TaskCreationOptions.RunContinuationsAsynchronously);
        public readonly ConcurrentDictionary<string, bool> Arrivals = new();
    }

    public static void Map(WebApplication app)
    {
        var gates = new ConcurrentDictionary<Guid, Gate>();
        app.MapPost("/gates", () =>
        {
            // A deliberately bounded local test fixture, not a public download service.
            if (gates.Count >= 16) return Results.StatusCode(429);
            var id = Guid.NewGuid();
            gates[id] = new Gate();
            return Results.Ok(new { id });
        });
        app.MapGet("/gates/{id:guid}", (Guid id) => gates.TryGetValue(id, out var gate)
            ? Results.Ok(new { arrived = gate.Arrivals.Keys.Order().ToArray(), released = gate.Release.Task.IsCompleted })
            : Results.NotFound());
        app.MapPost("/gates/{id:guid}/release", (Guid id) =>
        {
            if (!gates.TryGetValue(id, out var gate)) return Results.NotFound();
            gate.Release.TrySetResult();
            return Results.NoContent();
        });
        app.MapDelete("/gates/{id:guid}", (Guid id) =>
        {
            if (gates.TryRemove(id, out var gate)) gate.Release.TrySetCanceled();
            return Results.NoContent();
        });
        app.MapGet("/files/{name}", async (string name, Guid? gate, HttpContext context) =>
        {
            var artifact = Artifacts.FirstOrDefault(a => a.Name == name);
            if (artifact is null && name != "empty.bin" && name != "broken.bin")
            {
                context.Response.StatusCode = 404;
                return;
            }
            Gate? controlled = null;
            if (gate is { } id && !gates.TryGetValue(id, out controlled))
            {
                context.Response.StatusCode = 404;
                return;
            }
            byte[] bytes = artifact?.Bytes() ?? [];
            controlled?.Arrivals.TryAdd(name, true);
            context.Response.ContentType = "application/octet-stream";
            context.Response.ContentLength = name == "broken.bin" ? 100 : bytes.Length;
            await context.Response.StartAsync(context.RequestAborted);
            await context.Response.Body.FlushAsync(context.RequestAborted);
            if (controlled is not null)
            {
                await controlled.Release.Task.WaitAsync(context.RequestAborted);
            }
            if (name == "broken.bin")
            {
                context.Abort();
                return;
            }
            int chunk = artifact?.Chunk ?? 1;
            for (int offset = 0; offset < bytes.Length; offset += chunk)
            {
                await context.Response.Body.WriteAsync(bytes.AsMemory(offset, Math.Min(chunk, bytes.Length - offset)), context.RequestAborted);
                await context.Response.Body.FlushAsync(context.RequestAborted);
                await Task.Delay(2, context.RequestAborted);
            }
        });
    }
}
