using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using System.Reflection;

var syntax = CSharpSyntaxTree.ParseText("""
interface I { int Count { get; } }
class Base<T> : I { public virtual int Count => 1; }
sealed class Derived<T> : Base<T> { public override int Count => 0; }
sealed class Hidden<T> : Base<T> { public new int Count => 4; }
sealed class Reimplemented<T> : Base<T>, I { int I.Count => 5; }
class Other<T> {}
class Outer<T> { public class Inner {} }
class Probe<T> { }
class Buffer
{
    int[] data = new int[1];
    public void CopyOut(int[] target) => System.Array.Copy(data, 0, target, 0, 1);
    public void CopyNamed(int[] target) =>
        System.Array.Copy(destinationArray: target, sourceArray: data, length: 1);
    public void CopyIn(int[] source) => System.Array.Copy(source, 0, data, 0, 1);
    public void Move() => System.Array.Copy(data, 0, data, 0, 1);
    public void AliasedDestination()
    {
        int[] alias = data;
        System.Array.Copy(data, 0, alias, 0, 1);
    }
}
""");
var references = ((string)AppContext.GetData("TRUSTED_PLATFORM_ASSEMBLIES")!).Split(Path.PathSeparator)
    .Select(p => MetadataReference.CreateFromFile(p));
var compilation = CSharpCompilation.Create("NominalProbe", [syntax], references,
    new CSharpCompilationOptions(OutputKind.DynamicallyLinkedLibrary));
var errors = compilation.GetDiagnostics().Where(d => d.Severity == DiagnosticSeverity.Error).ToArray();
if (errors.Length != 0) throw new Exception(string.Join("\n", errors.Select(e => e.ToString())));
var implementation = typeof(Pal.Compiler.Frontend.Declarations).Assembly
    .GetType("Pal.Compiler.Frontend.NominalDispatch", throwOnError: true)!;
object? Invoke(string name, params object[] args) =>
    implementation.GetMethod(name, BindingFlags.Static | BindingFlags.Public)!.Invoke(null, args);
INamedTypeSymbol Type(string name) => compilation.GetTypeByMetadataName(name)!;
var integer = compilation.GetSpecialType(SpecialType.System_Int32);
var boolean = compilation.GetSpecialType(SpecialType.System_Boolean);
var variable = Type("Probe`1").TypeParameters[0];
var baseInt = Type("Base`1").Construct(integer);
IMethodSymbol Getter(INamedTypeSymbol type) =>
    type.GetMembers("Count").OfType<IPropertySymbol>().Single().GetMethod!;
void Expect(bool condition, string name)
{
    if (!condition) throw new Exception("Failed: " + name);
    Console.WriteLine("OK: " + name);
}
Expect(Invoke("Assignable", Type("Derived`1").Construct(integer), baseInt) is true, "derived assignability");
Expect(Invoke("Assignable", Type("Other`1").Construct(integer), baseInt) is false, "nominal disjointness");
Expect(Invoke("Assignable", Type("Derived`1").Construct(variable), baseInt) is null, "unknown generic instantiation");
Expect(Invoke("Assignable", Type("Derived`1").Construct(boolean), baseInt) is false, "different closed instantiation");
var slot = Getter(baseInt);
var derived = Type("Derived`1").Construct(integer);
Expect(SymbolEqualityComparer.Default.Equals((ISymbol?)Invoke("ClassSlot", derived, slot), Getter(derived)), "actual override");
var hidden = Type("Hidden`1").Construct(integer);
Expect(SymbolEqualityComparer.Default.Equals((ISymbol?)Invoke("ClassSlot", hidden, slot), slot), "new is not override");
var reimplemented = Type("Reimplemented`1").Construct(integer);
var iface = Type("I").GetMembers("Count").Single();
var actual = (IMethodSymbol)Invoke("InterfaceSlot", reimplemented, iface)!;
Expect(!SymbolEqualityComparer.Default.Equals(actual, slot) && actual.ExplicitInterfaceImplementations.Length == 1,
    "actual reimplemented interface slot");
Expect(SymbolEqualityComparer.Default.Equals((ISymbol?)Invoke("ClassSlot", reimplemented, slot), slot),
    "interface reimplementation does not replace class slot");
INamedTypeSymbol Inner(ITypeSymbol argument) =>
    Type("Outer`1").Construct(argument).GetTypeMembers("Inner").Single();
Expect(Invoke("Assignable", Inner(integer), Inner(boolean)) is false, "enclosing generic instantiation matters");
Expect(Invoke("Assignable", Inner(variable), Inner(integer)) is null, "enclosing unknown instantiation");
Expect(Invoke("Assignable", Inner(integer), Inner(integer)) is true, "same nested runtime class");
bool ReadOnly(string name) => Pal.Compiler.Frontend.Declarations.IsReadOnly(
    Type("Buffer").GetMembers(name).OfType<IMethodSymbol>().Single(), compilation);
Expect(ReadOnly("CopyOut"), "Array.Copy preserves source owner");
Expect(ReadOnly("CopyNamed"), "named Array.Copy arguments preserve source owner");
Expect(!ReadOnly("CopyIn"), "Array.Copy mutates destination owner");
Expect(!ReadOnly("Move"), "overlapping Array.Copy mutates owner");
Expect(!ReadOnly("AliasedDestination"), "aliased Array.Copy destination mutates owner");
// There is intentionally no test that calls Assignable on a mere static source
// and treats its result as an installed descriptor: this API requires exactness.
