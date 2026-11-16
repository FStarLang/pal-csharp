using System.Net.Http.Json;
using System.Security.Cryptography;
using System.Text.Json;
using AsyncDownloads;

using var client = new HttpClient { BaseAddress = new Uri(args[0]), Timeout = TimeSpan.FromSeconds(15) };
using var deadline = new CancellationTokenSource(TimeSpan.FromSeconds(45));
var token = deadline.Token;
byte[] Expected(int count, int seed) => Enumerable.Range(0, count).Select(i => (byte)((17 * i + seed) % 256)).ToArray();
void Check(bool condition, string message) { if (!condition) throw new Exception(message); }
async Task<Guid> NewGate()
{
    using var response = await client.PostAsync("gates", null, token);
    response.EnsureSuccessStatusCode();
    using var json = JsonDocument.Parse(await response.Content.ReadAsStringAsync(token));
    return json.RootElement.GetProperty("id").GetGuid();
}
Uri File(string name, Guid? gate = null) =>
    new(client.BaseAddress!, $"files/{name}" + (gate is null ? "" : $"?gate={gate}"));

var id = await NewGate();
try
{
    using var first = await Source.OpenAsync(client, File("amber.bin", id), token);
    using var second = await Source.OpenAsync(client, File("blue.bin", id), token);
    byte[] a = new byte[first.Length], b = new byte[second.Length];
    Task<int> pair = Transfers.Pair(first, a, second, b);
    Check(first.ReadsStarted == 1 && second.ReadsStarted == 1 && !pair.IsCompleted,
        "Both verified downloads must start a pending read before either is released.");
    using var status = JsonDocument.Parse(await client.GetStringAsync($"gates/{id}", token));
    Check(status.RootElement.GetProperty("arrived").GetArrayLength() == 2, "Both HTTP requests must reach their gates.");
    using var release = await client.PostAsync($"gates/{id}/release", null, token);
    release.EnsureSuccessStatusCode();
    Check(await pair.WaitAsync(token) == 10240, "Fan-out returned the wrong byte total.");
    Check(a.SequenceEqual(Expected(4096, 19)) && b.SequenceEqual(Expected(6144, 73)), "Downloaded bytes changed.");
}
finally
{
    using var removed = await client.DeleteAsync($"gates/{id}", token);
    removed.EnsureSuccessStatusCode();
}

using (var empty = await Source.OpenAsync(client, File("empty.bin"), token))
{
    Check(await Transfers.Download(empty, []) == 0 && empty.ReadsStarted == 0, "Empty download must need no read.");
}
using (var bounded = await Source.OpenAsync(client, File("amber.bin"), token))
{
    byte[] prefix = new byte[37];
    Check(await Transfers.Download(bounded, prefix) == 37, "A full destination must stop the download.");
    Check(prefix.SequenceEqual(Expected(37, 19)), "Bounded download lost its prefix.");
}
using (var eof = await Source.OpenAsync(client, File("amber.bin"), token))
{
    byte[] larger = new byte[4113];
    Check(await Transfers.Download(eof, larger) == 4096, "EOF must return the initialized prefix length.");
    Check(larger.AsSpan(0, 4096).SequenceEqual(Expected(4096, 19)) &&
          larger.AsSpan(4096).ToArray().All(x => x == 0), "EOF changed the unused tail.");
}

id = await NewGate();
try
{
    using var cancel = CancellationTokenSource.CreateLinkedTokenSource(token);
    using var first = await Source.OpenAsync(client, File("amber.bin", id), cancel.Token);
    using var second = await Source.OpenAsync(client, File("blue.bin", id), cancel.Token);
    Task<int> left = Transfers.Download(first, new byte[first.Length]);
    Task<int> right = Transfers.Download(second, new byte[second.Length]);
    cancel.Cancel();
    try
    {
        await Task.WhenAll(left, right).WaitAsync(token);
        throw new Exception("Cancelled reads returned success.");
    }
    catch (OperationCanceledException) when (cancel.IsCancellationRequested)
    {
        Check(left.IsCompleted && right.IsCompleted, "Cancellation must drain both children before disposal.");
    }
}
finally
{
    using var removed = await client.DeleteAsync($"gates/{id}", token);
    removed.EnsureSuccessStatusCode();
}

bool failed = false;
try
{
    using var broken = await Source.OpenAsync(client, File("broken.bin"), token);
    await Transfers.Download(broken, new byte[broken.Length]).WaitAsync(token);
}
catch (Exception error) when (error is HttpRequestException or IOException) { failed = true; }
Check(failed, "A truncated HTTP response must fail, not masquerade as a completed file.");

using var web = new HttpClient { BaseAddress = new Uri(args[1]), Timeout = TimeSpan.FromSeconds(15) };
using var result = await web.PostAsync("api/downloads", null, token);
result.EnsureSuccessStatusCode();
using var summary = JsonDocument.Parse(await result.Content.ReadAsStringAsync(token));
Check(summary.RootElement.GetProperty("totalBytes").GetInt32() == 10240, "Web byte total is incorrect.");
var downloads = summary.RootElement.GetProperty("downloads");
Check(downloads.GetArrayLength() == 2, "Web response must contain both downloads.");
Check(downloads[0].GetProperty("sha256").GetString() == Convert.ToHexString(SHA256.HashData(Expected(4096, 19))) &&
      downloads[1].GetProperty("sha256").GetString() == Convert.ToHexString(SHA256.HashData(Expected(6144, 73))),
      "Web checksums do not describe the downloaded bytes.");
Console.WriteLine("HTTP async: gated concurrent reads, exact bytes, capacity, EOF, empty input, cancellation, truncation, and web summary OK.");
