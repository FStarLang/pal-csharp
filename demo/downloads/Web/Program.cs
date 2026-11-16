using System.Diagnostics;
using System.Security.Cryptography;
using AsyncDownloads;
using AsyncDownloads.Web;

var builder = WebApplication.CreateBuilder(args);
var fixtureBase = new Uri(builder.Configuration["FixtureBase"] ?? "http://127.0.0.1:5081/");
builder.Services.AddSingleton(new HttpClient(new SocketsHttpHandler { AllowAutoRedirect = false })
{
    BaseAddress = fixtureBase,
    Timeout = TimeSpan.FromSeconds(30)
});
var app = builder.Build();
app.MapGet("/health", () => Results.Ok(new { ok = true }));

if (builder.Configuration.GetValue<bool>("fixture"))
{
    Fixture.Map(app);
}
else
{
    app.UseDefaultFiles();
    app.UseStaticFiles();
    app.MapPost("/api/downloads", async (HttpClient client, HttpContext context, ILogger<Program> logger) =>
    {
        var clock = Stopwatch.StartNew();
        using var cancellation = CancellationTokenSource.CreateLinkedTokenSource(context.RequestAborted);
        cancellation.CancelAfter(TimeSpan.FromSeconds(30));
        try
        {
            using var first = await Source.OpenAsync(client, new Uri(client.BaseAddress!, "files/amber.bin"), cancellation.Token);
            using var second = await Source.OpenAsync(client, new Uri(client.BaseAddress!, "files/blue.bin"), cancellation.Token);
            byte[] a = new byte[first.Length], b = new byte[second.Length];

            // WhenAll drains both children even on a fault, before their sources are
            // disposed. This recovery coordinator is outside the verified fragment.
            var counts = await Task.WhenAll(Transfers.Download(first, a), Transfers.Download(second, b));
            var buffers = new[] { a, b };
            var results = Fixture.Artifacts.Select((artifact, i) => new
            {
                name = artifact.Name,
                bytes = counts[i],
                sha256 = Convert.ToHexString(SHA256.HashData(buffers[i].AsSpan(0, counts[i]))),
                matches = counts[i] == artifact.Length && buffers[i].AsSpan(0, counts[i]).SequenceEqual(artifact.Bytes())
            }).ToArray();
            if (results.Any(r => !r.matches))
                throw new InvalidDataException("Downloaded bytes differ from the configured fixture.");
            return Results.Ok(new
            {
                elapsedMs = clock.ElapsedMilliseconds,
                totalBytes = counts.Sum(),
                reads = first.ReadsStarted + second.ReadsStarted,
                downloads = results
            });
        }
        catch (Exception error) when (error is HttpRequestException or IOException or OperationCanceledException)
        {
            logger.LogWarning(error, "Download did not complete.");
            return Results.Problem("Download failed or was cancelled; no completed result is published.", statusCode: 502);
        }
    });
}

app.Run();
