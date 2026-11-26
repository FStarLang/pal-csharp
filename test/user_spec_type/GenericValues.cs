using System;
using PalLang;

[assembly: IncludePulse("GenericSpecValues", """
module GenericSpecValues
module S = FStar.Seq

let identity (#a:Type0) (x:a) : a = x

let check (#a:Type0) (s:S.seq a) (x:a) (i:int)
  : Lemma
    (requires i == 0 /\ S.length s > 0 /\ S.index s 0 == x)
    (ensures True)
  = ()
""")]

namespace PalCSharp.Tests;

public static class GenericValueOperations
{
    [SpecOp("GenericSpecValues.identity")]
    public static T Identity<T>(T value) => throw new InvalidOperationException();

    [SpecOp("GenericSpecValues.check")]
    public static void Check<T>(Seq<T> items, T value, SpecInt index) =>
        throw new InvalidOperationException();
}

public static class GenericValues
{
    [Ensures("Result == value")]
    public static int Variable(int value)
    {
        int[] items = new int[1];
        items[0] = value;
        GenericValueOperations.Check(Pal.Contents(items), value, 0);
        Pal.Assert(Pal.Same(GenericValueOperations.Identity(value), value));
        return value;
    }

    [Ensures("true")]
    public static void Literal()
    {
        int[] items = new int[1];
        items[0] = 2;
        GenericValueOperations.Check(Pal.Contents(items), 2, 0);
        Pal.Assert(Pal.Same(GenericValueOperations.Identity(2), 2));
    }

    [Ensures("Result == value")]
    public static long Wide(long value)
    {
        long[] items = new long[1];
        items[0] = value;
        int index = 0;
        GenericValueOperations.Check(Pal.Contents(items), value, index);
        Pal.Assert(Pal.Same(GenericValueOperations.Identity(value), value));
        return value;
    }
}
