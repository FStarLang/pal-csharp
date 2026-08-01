using System.Reflection;
using System.Reflection.Emit;

namespace PalCSharp.Test;

/// <summary>
/// Checks the non-negotiable core invariant of pal-csharp: annotated C#
/// compiles and runs unmodified, and in a build where <c>PAL</c> is not
/// defined the annotations leave no trace in the emitted IL.
/// </summary>
public static class Program
{
    private static int _failures;

    public static int Main()
    {
        CheckDecoderWorks();
        CheckBehaviourUnchanged();
        CheckAnnotationsErased();
        CheckAttributesArePresent();
        CheckGhostArgumentIsOptional();

        Console.WriteLine(_failures == 0
            ? "annotations: OK"
            : $"annotations: {_failures} failure(s)");
        return _failures == 0 ? 0 : 1;
    }

    private static void Check(bool condition, string what)
    {
        if (!condition)
        {
            _failures++;
            Console.Error.WriteLine($"FAIL: {what}");
        }
    }

    // -- 0. The detector itself detects. ------------------------------------
    //
    // Without this, "no PalLang call was found" would be satisfied vacuously by
    // an IL decoder that finds nothing at all.

    private static void CheckDecoderWorks()
    {
        var main = typeof(Program).GetMethod(nameof(Main))!;
        Check(CalleesOf(main).Any(m => m.Name == nameof(CheckAnnotationsErased)),
              "the IL decoder finds an ordinary call");

        // A [Spec] body is the one place a PalLang call is expected to survive,
        // so it doubles as a positive control for the erasure check.
        var sorted = typeof(Annotated).GetMethod(nameof(Annotated.Sorted))!;
        Check(CalleesOf(sorted).Any(m => m.DeclaringType?.Namespace == "PalLang"),
              "the IL decoder finds a PalLang call when one is present");
    }

    // -- 1. The annotated code still runs, and computes the right answers. --

    private static void CheckBehaviourUnchanged()
    {
        int x = 3, y = 7;
        Annotated.Swap(ref x, ref y);
        Check(x == 7 && y == 3, "Swap swaps");

        Check(Annotated.Max(3, 7) == 7, "Max picks the larger");

        Annotated.DivMod(17, 5, out int q, out int r);
        Check(q == 3 && r == 2, "DivMod computes 17 = 3*5 + 2");

        Check(Annotated.CountPositive([1, -2, 3, 0, 4]) == 3, "CountPositive counts");

        int[] a = [5, 2, 9, 1, 5, 6];
        Annotated.InsertionSort(a);
        Check(a is [1, 2, 5, 5, 6, 9], "InsertionSort sorts");

        Check(Annotated.Identity(42) == 42, "Identity with an omitted ghost argument");
    }

    // -- 2. No annotation survives into the IL. -----------------------------

    private static void CheckAnnotationsErased()
    {
        foreach (var method in typeof(Annotated).GetMethods(
                     BindingFlags.Public | BindingFlags.NonPublic | BindingFlags.Static))
        {
            // A [Spec] function's own body is specification-only; it is never
            // executed and is expected to mention Pal.
            if (method.GetCustomAttributes().Any(attr => attr.GetType().Name == "SpecAttribute"))
                continue;

            foreach (var callee in CalleesOf(method))
            {
                Check(callee.DeclaringType?.Namespace != "PalLang",
                      $"{method.Name} still calls {callee.DeclaringType?.Name}.{callee.Name}");
            }
        }

        // A [Conditional("PAL")] lemma erases its call sites, so the sorted
        // loop body must contain no call at all beyond the array accesses.
        var sort = typeof(Annotated).GetMethod(nameof(Annotated.InsertionSort))!;
        Check(!CalleesOf(sort).Any(), $"InsertionSort emits calls: " +
              string.Join(", ", CalleesOf(sort).Select(m => m.Name)));
    }

    // -- 3. But the attributes themselves are still there, for the tool. ----

    private static void CheckAttributesArePresent()
    {
        var swap = typeof(Annotated).GetMethod(nameof(Annotated.Swap))!;
        var ensures = swap.GetCustomAttributes()
                          .Where(a => a.GetType().Name == "EnsuresAttribute").ToList();
        Check(ensures.Count == 1, "Swap carries exactly one [Ensures]");

        var sort = typeof(Annotated).GetMethod(nameof(Annotated.InsertionSort))!;
        Check(sort.GetCustomAttributes().Count(a => a.GetType().Name == "EnsuresAttribute") == 2,
              "InsertionSort carries two [Ensures]");

        var lemma = typeof(Annotated).GetMethod(nameof(Annotated.PermSwap))!;
        Check(lemma.GetCustomAttributes().Any(a => a.GetType().Name == "LemmaAttribute"),
              "PermSwap is marked [Lemma]");
    }

    // -- 4. Ghost parameters are optional and free. -------------------------

    private static void CheckGhostArgumentIsOptional()
    {
        var identity = typeof(Annotated).GetMethod(nameof(Annotated.Identity))!;
        var ghost = identity.GetParameters()[1];
        Check(ghost.IsOptional, "the Ghost<T> parameter is optional");
        Check(ghost.ParameterType.IsValueType, "Ghost<T> is a value type");
        Check(ghost.ParameterType.GetFields(
                  BindingFlags.Instance | BindingFlags.Public | BindingFlags.NonPublic).Length == 0,
              "Ghost<T> has no fields");
    }

    // -- IL scanning --------------------------------------------------------

    private static readonly Dictionary<short, OpCode> Opcodes =
        typeof(OpCodes)
            .GetFields(BindingFlags.Public | BindingFlags.Static)
            .Where(f => f.FieldType == typeof(OpCode))
            .Select(f => (OpCode)f.GetValue(null)!)
            .ToDictionary(op => op.Value);

    /// <summary>
    /// Every method referenced by a <c>call</c>, <c>callvirt</c>, <c>newobj</c>
    /// or <c>ldftn</c> in the body of <paramref name="method"/>.
    /// </summary>
    /// <remarks>
    /// The IL is decoded instruction by instruction using the operand sizes
    /// from <see cref="OpCodes"/>, so operand bytes are never mistaken for
    /// opcodes.
    /// </remarks>
    private static List<MethodBase> CalleesOf(MethodBase method)
    {
        var result = new List<MethodBase>();
        byte[]? il = method.GetMethodBody()?.GetILAsByteArray();
        if (il is null) return result;

        var module = method.Module;
        var typeArgs = method.DeclaringType?.IsGenericType == true
            ? method.DeclaringType.GetGenericArguments() : null;
        var methodArgs = method.IsGenericMethodDefinition
            ? method.GetGenericArguments() : null;

        int pc = 0;
        while (pc < il.Length)
        {
            bool twoByte = il[pc] == 0xFE && pc + 1 < il.Length;
            short code = twoByte ? unchecked((short)(0xFE00 | il[pc + 1])) : il[pc];
            pc += twoByte ? 2 : 1;

            if (!Opcodes.TryGetValue(code, out var op))
                break; // undecodable: stop rather than misreport

            switch (op.OperandType)
            {
                case OperandType.InlineNone:
                    break;
                case OperandType.ShortInlineBrTarget:
                case OperandType.ShortInlineI:
                case OperandType.ShortInlineVar:
                    pc += 1;
                    break;
                case OperandType.InlineVar:
                    pc += 2;
                    break;
                case OperandType.InlineI8:
                case OperandType.InlineR:
                    pc += 8;
                    break;
                case OperandType.InlineSwitch:
                    int n = BitConverter.ToInt32(il, pc);
                    pc += 4 + 4 * n;
                    break;
                default:
                    if (op.OperandType is OperandType.InlineMethod or OperandType.InlineTok)
                    {
                        int token = BitConverter.ToInt32(il, pc);
                        try
                        {
                            if (module.ResolveMethod(token, typeArgs, methodArgs) is { } callee)
                                result.Add(callee);
                        }
                        catch (ArgumentException) { }
                    }
                    pc += 4;
                    break;
            }
        }

        return result;
    }
}
