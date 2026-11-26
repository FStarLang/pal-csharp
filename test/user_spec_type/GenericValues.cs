using System;
using System.Diagnostics;
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

    [Ensures("Result == value")]
    public static int CheckedIdentity(int value)
    {
        Pal.Assert(Identity(value) == value);
        return value;
    }
}

public static class GenericValues
{
    [Lemma, Conditional("PAL"), Requires("!flag")]
    public static void FalseWitness(Ghost<bool> flag) => Pal.Assert(!flag.Value);

    [Lemma, Conditional("PAL"), Requires("flag")]
    public static void TrueWitness(Ghost<bool> flag) => Pal.Assert(flag.Value);

    [Ensures("Result")]
    public static bool BooleanWitnesses()
    {
        FalseWitness(false);
        TrueWitness(true);
        return true;
    }

    [Ensures("Result == value")]
    public static int Variable(int value)
    {
        int[] items = new int[1];
        items[0] = value;
        GenericValueOperations.Check(Pal.Contents(items), value, 0);
        Pal.Assert(Pal.Same(GenericValueOperations.Identity(value), value));
        return GenericValueOperations.CheckedIdentity(value);
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
