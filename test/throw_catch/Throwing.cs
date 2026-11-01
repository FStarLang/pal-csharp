// §19. Exceptions. A `throw` is Pulse's `raise`, a `try`/`catch` is Pulse's `try`, and a
// method says what it may throw with `[Throws]`: the class, and what holds when it does.
// A method that declares nothing must be proved never to throw, so every handler below
// is checked to have caught everything its callee can raise.
using System;
using PalLang;

/// <summary>A base class: abstract, so it is caught but never thrown as itself.</summary>
public abstract class AppError : Exception
{
    public int Code { get; }
    protected AppError(int code) { Code = code; }
}

public sealed class RangeError : AppError
{
    public int Index { get; }
    public RangeError(int code, int index) : base(code) { Index = index; }
}

public sealed class LimitError : AppError
{
    public LimitError() : base(25) { }
}

public static class Throwing
{
    /// <summary>A guard: the exception is thrown exactly when the argument is negative.</summary>
    [Ensures("Result == x && x >= 0")]
    [Throws(typeof(RangeError), "x < 0 && Thrown.Code == 1 && Thrown.Index == 0")]
    public static int NonNegative(int x)
    {
        if (x < 0)
        {
            throw new RangeError(1, 0);
        }
        return x;
    }

    /// <summary>Two exception classes, one of them thrown from inside a loop.</summary>
    [Requires("a.Length <= 1000")]
    [Ensures("Result >= 0")]
    [Throws(typeof(LimitError), "a.Length > 25 && Thrown.Code == 25")]
    [Throws(typeof(RangeError), "Thrown.Code == 2 && 0 <= Thrown.Index && Thrown.Index < a.Length && Contents(a)[Thrown.Index] < 0")]
    public static int CheckAll(int[] a)
    {
        if (a.Length > 25)
        {
            throw new LimitError();
        }
        int count = 0;
        for (int i = 0; i < a.Length; i++)
        {
            Pal.Invariant(0 <= i && i <= a.Length && 0 <= count && count <= i);
            if (a[i] < 0)
            {
                throw new RangeError(2, i);
            }
            count = count + 1;
        }
        return count;
    }

    /// <summary>
    /// A handler for the base class catches both subclasses, and reads the field they
    /// share. A handler knows the class of what it caught and nothing more, so the field
    /// is tested rather than trusted. Nothing escapes, and that is proved: `[Throws]` is
    /// absent.
    /// </summary>
    [Requires("a.Length <= 1000")]
    [Ensures("Result >= 0 - 2")]
    public static int Classify(int[] a)
    {
        int result = 0;
        try
        {
            Pal.Invariant(result >= 0 - 2);
            result = CheckAll(a);
        }
        catch (AppError e)
        {
            if (e.Code == 25)
            {
                result = 0 - 2;
            }
            else
            {
                result = 0 - 1;
            }
        }
        return result;
    }

    /// <summary>
    /// A filtered handler, and a rethrow. The filter takes only one kind of
    /// `RangeError`; the rest propagate. A handler knows the class of what it caught and
    /// nothing else (R19.3), so a rethrow promises only the class.
    /// </summary>
    [Ensures("Result >= 0")]
    [Throws(typeof(RangeError))]
    public static int Recover(int x, bool rethrow)
    {
        int result = 0;
        try
        {
            Pal.Invariant(result >= 0);
            result = NonNegative(x);
        }
        catch (RangeError e) when (e.Index > 0)
        {
            result = e.Index;
        }
        catch (RangeError)
        {
            if (rethrow)
            {
                throw;
            }
            result = 0;
        }
        return result;
    }
}
