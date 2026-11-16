using System.Collections.Immutable;
using System.Security.Cryptography;
using System.Text;
using System.Text.Json;
using Microsoft.CodeAnalysis.CSharp;
using Pal.Compiler.Diagnostics;
using Pal.Compiler.Emit;
using Pal.Compiler.Ir;
using Pal.Compiler.Passes;

namespace Pal.Compiler.Frontend;

/// <summary>
/// R36.1. What a translation leaves in its output directory about itself, so that a later
/// translation can reference it: the sources it was translated from, as they were then;
/// how they were compiled; the units it referenced in turn; and the modules it emitted.
/// </summary>
public sealed class UnitManifest
{
    public const string FileName = "unit.json";

    public string Assembly { get; set; } = "";
    public bool Nullable { get; set; } = true;
    public bool Preview { get; set; }
    public bool Unsafe { get; set; }
    public List<UnitSource> Sources { get; set; } = [];
    public List<string> References { get; set; } = [];
    public List<string> Modules { get; set; } = [];

    private static readonly JsonSerializerOptions Options = new()
    {
        WriteIndented = true,
        PropertyNamingPolicy = JsonNamingPolicy.CamelCase,
    };

    public string ToJson() => JsonSerializer.Serialize(this, Options);

    public static UnitManifest? Read(string dir)
    {
        var path = Path.Combine(dir, FileName);
        return File.Exists(path) ? JsonSerializer.Deserialize<UnitManifest>(File.ReadAllText(path), Options) : null;
    }

    /// <summary>
    /// R36.2. A unit's assembly name is a function of where it is written, so that two units
    /// of one build never share one and a unit is named the same in every build it is in.
    /// </summary>
    public static string AssemblyFor(string outputDir) =>
        "PalUnit_" + Hash(Encoding.UTF8.GetBytes(Path.GetFullPath(outputDir))).Substring(0, 16);

    public static string Hash(byte[] bytes)
    {
        using var sha = SHA256.Create();
        return string.Concat(sha.ComputeHash(bytes).Select(b => b.ToString("x2")));
    }

    public static UnitSource Source(string path) =>
        new() { Path = System.IO.Path.GetFullPath(path), Sha256 = Hash(File.ReadAllBytes(path)) };
}

public sealed class UnitSource
{
    public string Path { get; set; } = "";
    public string Sha256 { get; set; } = "";
}

/// <summary>
/// §36. The units a translation references, compiled and lowered again so that the primary
/// unit's frontend and emitter see them exactly as they would see the same declarations in
/// one program — and nothing of them is emitted again.
/// </summary>
public sealed class UnitGraph
{
    public sealed record Unit(string Dir, UnitManifest Manifest, ImmutableArray<string> Deps)
    {
        public CSharpCompilation? Compilation { get; set; }
        public ImmutableArray<IrDecl> Ir { get; set; } = [];
    }

    /// <summary>Every referenced unit, each after the units it references.</summary>
    public ImmutableArray<Unit> Units { get; }

    /// <summary>The units named on the command line.</summary>
    public ImmutableArray<string> Direct { get; }

    private UnitGraph(ImmutableArray<Unit> units, ImmutableArray<string> direct)
    {
        Units = units;
        Direct = direct;
    }

    /// <summary>
    /// R36.1. Reads the manifests of <paramref name="dirs"/> and, transitively, of the units
    /// they reference. A unit without a manifest, or whose sources changed after it was
    /// translated, is refused: what it was verified as is no longer what it is.
    /// </summary>
    public static UnitGraph Load(IEnumerable<string> dirs, out string? error)
    {
        error = null;
        var byDir = new Dictionary<string, Unit>(StringComparer.Ordinal);
        var order = ImmutableArray.CreateBuilder<Unit>();
        var visiting = new HashSet<string>(StringComparer.Ordinal);
        var direct = dirs.Select(Path.GetFullPath).Distinct().ToImmutableArray();

        string? Visit(string dir)
        {
            if (byDir.ContainsKey(dir)) return null;
            if (!visiting.Add(dir)) return $"the references of `{dir}` form a cycle";
            UnitManifest? manifest;
            try
            {
                manifest = UnitManifest.Read(dir);
            }
            catch (JsonException e)
            {
                return $"`{dir}` has an invalid {UnitManifest.FileName}: {e.Message}";
            }
            if (manifest is null)
                return $"`{dir}` has no {UnitManifest.FileName}: it is not the output of a translation";
            foreach (var s in manifest.Sources)
                if (!File.Exists(s.Path) || UnitManifest.Hash(File.ReadAllBytes(s.Path)) != s.Sha256)
                    return $"`{dir}` is stale: `{s.Path}` changed after it was translated; translate it again";
            foreach (var r in manifest.References)
                if (Visit(r) is { } e) return e;
            visiting.Remove(dir);
            var unit = new Unit(dir, manifest, [.. manifest.References]);
            byDir[dir] = unit;
            order.Add(unit);
            return null;
        }

        foreach (var d in direct)
            if (Visit(d) is { } e) { error = e; break; }
        return new UnitGraph(order.ToImmutable(), direct);
    }

    private ImmutableArray<Unit> Closure(IEnumerable<string> dirs)
    {
        var seen = new HashSet<string>(StringComparer.Ordinal);
        var work = new Stack<string>(dirs);
        while (work.Count > 0)
        {
            var d = work.Pop();
            if (!seen.Add(d)) continue;
            foreach (var r in Units.First(u => u.Dir == d).Deps) work.Push(r);
        }
        return [.. Units.Where(u => seen.Contains(u.Dir))];
    }

    /// <summary>The referenced units' compilations, for the primary unit to reference.</summary>
    public IEnumerable<CSharpCompilation> Compilations => Closure(Direct).Select(u => u.Compilation!);

    /// <summary>R36.3. Every declaration of every unit the primary unit references, transitively.</summary>
    public ImmutableArray<IrDecl> Context => [.. Closure(Direct).SelectMany(u => u.Ir)];

    /// <summary>
    /// R36.2. Compiles each unit against the compilations of the units it references, with
    /// its <c>internal</c>s open to every unit of the build, <paramref name="client"/>
    /// included. Returns the C# errors of the first unit that has any.
    /// </summary>
    public IReadOnlyList<Microsoft.CodeAnalysis.Diagnostic> Compile(string client)
    {
        var names = Units.Select(u => u.Manifest.Assembly).Append(client).ToList();
        foreach (var u in Units)
        {
            var m = u.Manifest;
            u.Compilation = Loader.Create(
                m.Sources.Select(s => s.Path), m.Assembly, m.Nullable, m.Preview, m.Unsafe,
                Closure(u.Deps).Select(d => d.Compilation!), names.Where(n => n != m.Assembly));
            var errors = u.Compilation.GetDiagnostics()
                .Where(d => d.Severity == Microsoft.CodeAnalysis.DiagnosticSeverity.Error).ToList();
            if (errors.Count > 0) return errors;
        }
        return [];
    }

    /// <summary>
    /// R36.3. Lowers each unit, in order, with the declarations of the units it references
    /// as its context — the same passes its own translation ran, so the same declarations.
    /// A unit that does not translate cleanly cannot be referenced: returns its directory.
    /// </summary>
    public string? Lower(out DiagnosticBag failed)
    {
        foreach (var u in Units)
        {
            var bag = new DiagnosticBag();
            var context = (ImmutableArray<IrDecl>)[.. Closure(u.Deps).SelectMany(d => d.Ir)];
            var ir = FrontendPass.Run(u.Compilation!, bag, context);
            ir = Normalize.Run(ir, bag);
            ir = Check.Run(ir, bag, context);
            u.Ir = ir.Declarations;
            if (bag.HasErrors) { failed = bag; return u.Dir; }
        }
        failed = new DiagnosticBag();
        return null;
    }

    /// <summary>
    /// R36.4. A module is emitted by one unit. A module of the primary unit, or of one
    /// referenced unit, named as a module another referenced unit emitted, would be two
    /// modules F* cannot tell apart — and it would check only one of them.
    /// </summary>
    public void CheckCollisions(ImmutableArray<EmittedModule> modules, DiagnosticBag diagnostics)
    {
        var owner = new Dictionary<string, string>(StringComparer.OrdinalIgnoreCase);
        foreach (var u in Closure(Direct))
            foreach (var name in u.Manifest.Modules)
            {
                if (owner.TryGetValue(name, out var other) && other != u.Dir)
                    diagnostics.Error("PALCS0758", IrLoc.None,
                        $"module `{name}` is emitted both by referenced unit `{other}` and by " +
                        $"referenced unit `{u.Dir}`; a module can belong to one unit only " +
                        "(doc/translation.md R36.4). Translate the declaration in one of them, " +
                        "or rename one of the two.");
                owner[name] = u.Dir;
            }
        foreach (var m in modules)
            if (owner.TryGetValue(m.Name, out var dir))
                diagnostics.Error("PALCS0758", m.Origin.IsDefaultOrEmpty ? IrLoc.None : m.Origin[0].Loc,
                    $"module `{m.Name}` is already emitted by referenced unit `{dir}`; the same " +
                    "declaration is translated twice, or two declarations share a name " +
                    "(doc/translation.md R36.4). Leave its source to the referenced unit, or rename it.");
    }
}
