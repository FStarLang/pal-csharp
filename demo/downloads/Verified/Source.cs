using System;
using System.IO;
using System.Net.Http;
using System.Threading;
using System.Threading.Tasks;
using PalLang;

[assembly: TranslateAnnotatedOnly]
[assembly: IncludePulseFile("DownloadIO.fst")]

namespace AsyncDownloads;

[SpecType("DownloadIO.source")]
public sealed class Source : IDisposable
{
    private readonly HttpResponseMessage response;
    internal readonly Stream Stream;
    internal readonly CancellationToken Cancellation;
    internal int ReadCount;
    public int ReadsStarted => Volatile.Read(ref ReadCount);
    public int Length { get; }

    private Source(HttpResponseMessage response, Stream stream, int length, CancellationToken cancellation)
    {
        this.response = response;
        Stream = stream;
        Length = length;
        Cancellation = cancellation;
    }

    [SpecOp("DownloadIO.contents")]
    public Seq<byte> Content => throw new InvalidOperationException("Specification only.");

    [SpecOp("DownloadIO.at")]
    public static SlProp At(Source source, SpecInt offset) => throw new InvalidOperationException();

    public static async Task<Source> OpenAsync(HttpClient client, Uri uri, CancellationToken cancellation)
    {
        var response = await client.GetAsync(uri, HttpCompletionOption.ResponseHeadersRead, cancellation);
        try
        {
            response.EnsureSuccessStatusCode();
            long? length = response.Content.Headers.ContentLength;
            if (length is null || length < 0 || length > 1_048_576)
                throw new InvalidDataException("A bounded Content-Length (0..1 MiB) is required.");
            var stream = await response.Content.ReadAsStreamAsync(cancellation);
            return new Source(response, stream, (int)length.Value, cancellation);
        }
        catch
        {
            response.Dispose();
            throw;
        }
    }

    public void Dispose() => response.Dispose();
}

public static class Input
{
    [Spec, PulseBody("DownloadIO.prefix $(input) $(output) $(n)")]
    public static bool Prefix(Seq<byte> input, Seq<byte> output, SpecInt n) => throw new InvalidOperationException();

#pragma warning disable PALCS0904
    [Implements("DownloadIO.read $(source) $&(target) $(offset)")]
    [Requires("Source.At(source, offset)")]
    [Requires("Prefix(source.Content, Contents(target), offset) && offset < target.Length")]
    [Ensures("0 <= Result && Result <= target.Length - offset")]
    [Ensures("Source.At(source, offset + Result)")]
    [Ensures("Prefix(source.Content, Contents(target), offset + Result)")]
    [Ensures("Pal.Iff(Result == 0, offset == source.Content.Length)")]
    public static async Task<int> Read(Source source, byte[] target, int offset)
    {
        Interlocked.Increment(ref source.ReadCount);
        return await source.Stream.ReadAsync(target.AsMemory(offset), source.Cancellation);
    }
#pragma warning restore PALCS0904
}
