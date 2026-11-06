namespace Pal.Compiler.Frontend;

/// <summary>
/// §27. Regions: the objects of a <c>[Region]</c> class, owned together by the translated
/// class that holds a field of it, through <c>Pulse.Lib.CSharp.Region</c>.
/// </summary>
public static class Region
{
    public const string Module = "Pulse.Lib.CSharp.Region";

    /// <summary>R27.16. The shape theory of written regions.</summary>
    public const string TreeModule = "Pulse.Lib.CSharp.RegionTree";

    /// <summary>The spec-scope name of the heap a method holds for a region class.</summary>
    public static string HeapName(string regionClass) => "$heap_" + regionClass;

    /// <summary>The F* binder an owner's invariant gives that heap.</summary>
    public static string HeapBinder(string regionClass) => "heap_" + regionClass;

    public static string LeftOf(string c) => "class_" + c + "__left";
    public static string RightOf(string c) => "class_" + c + "__right";
    public static string ViewOf(string c) => "class_" + c + "__view";
    public static string TreeOf(string c) => "class_" + c + "__tree";
    public static string WfOf(string c) => "class_" + c + "__wf";
    public static string ReadOf(string c) => "class_" + c + "__read";
    public static string UnsharedOf(string c) => "class_" + c + "__unshared";
    public static string ReshapedOf(string c) => "class_" + c + "__reshaped";
}
