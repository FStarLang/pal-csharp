// A Roslyn analyzer is loaded into whatever process is doing the compiling, and that
// process may be .NET Framework, so an analyzer assembly and everything it drags with it
// must be `netstandard2.0`.  Nothing in pal-csharp needs a newer *runtime*: what the
// compiler uses and netstandard2.0 lacks is six language and BCL conveniences, and they
// are all one file's worth of shim.  This file is that file, and it is `#if`'d so the
// net10.0 build sees none of it.
//
// Note that `LangVersion` is independent of the target framework: records, pattern
// matching, collection expressions and nullable annotations all work here, which is why
// the retarget touches no real code.

#if NETSTANDARD2_0
namespace System.Runtime.CompilerServices
{
    internal static class IsExternalInit { }
}
#endif
