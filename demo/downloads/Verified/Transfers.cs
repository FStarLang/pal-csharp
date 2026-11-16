using System.Threading.Tasks;
using PalLang;

namespace AsyncDownloads;

public static class Transfers
{
    [Requires("Source.At(source, 0)")]
    [Ensures("Source.At(source, Result)")]
    [Ensures("Input.Prefix(source.Content, Contents(target), Result)")]
    [Ensures("Result == target.Length || Result == source.Content.Length")]
    public static async Task<int> Download(Source source, byte[] target)
    {
        int offset = 0;
        bool more = true;
        while (offset < target.Length && more)
        {
            Pal.Invariant(Source.At(source, offset));
            Pal.Invariant(Input.Prefix(source.Content, Pal.Contents(target), offset));
            Pal.Invariant(more || offset == source.Content.Length);
            int received = await Input.Read(source, target, offset);
            offset += received;
            if (received == 0)
                more = false;
        }
        return offset;
    }

    [Requires("Source.At(first, 0)")]
    [Requires("Source.At(second, 0)")]
    [Requires("a.Length == first.Content.Length && b.Length == second.Content.Length")]
    [Requires("a.Length <= 1048576 && b.Length <= 1048576")]
    [Ensures("Source.At(first, a.Length)")]
    [Ensures("Source.At(second, b.Length)")]
    [Ensures("Input.Prefix(first.Content, Contents(a), a.Length)")]
    [Ensures("Input.Prefix(second.Content, Contents(b), b.Length)")]
    [Ensures("Result == a.Length + b.Length")]
    public static async Task<int> Pair(Source first, byte[] a, Source second, byte[] b)
    {
        Task<int> left = Download(first, a);
        Task<int> right = Download(second, b);
        int nr = await right;
        int nl = await left;
        return nl + nr;
    }
}
