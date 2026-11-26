using System.Reflection;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Pal.Compiler.Frontend;

var syntax = CSharpSyntaxTree.ParseText("""
using PalLang;
[Plain] sealed class Identity { public int Value; }
[Plain] sealed class Generic<T> { public T Value = default!; }
[Plain] class Open { }
[Plain] sealed class Override {
    public override bool Equals(object? o) => true;
    public override int GetHashCode() => 0;
}
[Plain] sealed class Equatable : System.IEquatable<Equatable> {
    bool System.IEquatable<Equatable>.Equals(Equatable? o) => true;
}
[Plain] sealed class OtherEquatable : System.IEquatable<int> {
    public bool Equals(int o) => true;
}
class Base { }
[Plain] sealed class Derived : Base { }
class OverrideBase {
    public override bool Equals(object? o) => true;
    public override int GetHashCode() => 0;
}
[Plain] sealed class InheritedOverride : OverrideBase { }
[Plain] sealed class Hidden {
    public new bool Equals(object? o) => true;
}
[Plain] sealed class HashOverride {
    public override int GetHashCode() => 42;
}
sealed class NotPlain { }
class Outer<T> { [Plain] public sealed class Nested { } }
""");
var references = ((string)AppContext.GetData("TRUSTED_PLATFORM_ASSEMBLIES")!)
    .Split(Path.PathSeparator)
    .Append(typeof(PalLang.PlainAttribute).Assembly.Location)
    .Distinct()
    .Select(p => MetadataReference.CreateFromFile(p));
var compilation = CSharpCompilation.Create("EqualityEligibility", [syntax], references,
    new CSharpCompilationOptions(OutputKind.DynamicallyLinkedLibrary));
var errors = compilation.GetDiagnostics().Where(d => d.Severity == DiagnosticSeverity.Error).ToArray();
if (errors.Length != 0)
    throw new Exception(string.Join("\n", errors.Select(d => d.ToString())));
var known = WellKnown.For(compilation);
var classifier = typeof(WellKnown).Assembly
    .GetType("Pal.Compiler.Frontend.DefaultEquality", throwOnError: true)!
    .GetMethod("IsReferenceIdentity", BindingFlags.Public | BindingFlags.Static)!;
void Check(string name, bool expected)
{
    var type = compilation.GetTypeByMetadataName(name)!;
    var actual = (bool)classifier.Invoke(null, [type, known])!;
    if (actual != expected)
        throw new Exception($"{name}: expected {expected}, got {actual}");
    Console.WriteLine($"OK: {name} -> {(actual ? "reference identity" : "opaque")}");
}
Check("Identity", true);
Check("Generic`1", true);
Check("Open", false);
Check("Override", false);
Check("Equatable", false);
Check("OtherEquatable", false);
Check("Derived", false);
Check("InheritedOverride", false);
Check("Hidden", true);
Check("HashOverride", true);
Check("NotPlain", false);
Check("Outer`1+Nested", true);
