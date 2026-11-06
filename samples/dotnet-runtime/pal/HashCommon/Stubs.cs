// Stand-ins for CoreLib internals that HashSet<T> and Dictionary<TKey, TValue> name but
// verified code does not reach (string-comparer randomization, serialization, obsoletion
// messages). They exist only so that the sources compile.
namespace System
{
    internal static class Obsoletions
    {
        internal const string SharedUrlFormat = "https://aka.ms/dotnet-warnings/{0}";
        internal const string LegacyFormatterImplMessage = "This API supports obsolete formatter-based serialization.";
        internal const string LegacyFormatterImplDiagId = "SYSLIB0051";
    }

    internal static class SR
    {
        internal const string Arg_HTCapacityOverflow = "Hashtable's capacity overflowed and went negative.";
        internal const string Argument_AddingDuplicateWithKey = "An item with the same key has already been added.";
        internal static string Format(string format, object? arg0) => format;
    }
}

namespace System.Collections.Generic
{
    // Stands in for CoreLib's comparer of the same name (public there, so this shadows it).
    public class NonRandomizedStringEqualityComparer : IEqualityComparer<string?>
    {
        public bool Equals(string? x, string? y) => string.Equals(x, y);
        public int GetHashCode(string? obj) => obj?.GetHashCode() ?? 0;
        internal virtual IEqualityComparer<string?> GetRandomizedEqualityComparer() => EqualityComparer<string?>.Default;
        public virtual IEqualityComparer<string?> GetUnderlyingEqualityComparer() => EqualityComparer<string?>.Default;
        public static IEqualityComparer<string>? GetStringComparer(object comparer) => null;
    }
}
