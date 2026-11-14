using System;
using System.Diagnostics;
using PalLang;

[assembly: IncludePulseFile("GhostWitness.fst")]

namespace PalCSharp.Tests;

public static class WitnessProof
{
    [Lemma, Requires("OwnerSpec.Cell(cell)")]
    [Ensures("OwnerSpec.Raw(cell, Result, Perm.Full)")]
    [PulseBody("GhostWitness.unpack $(cell)")]
    public static Ghost<CellSnapshot> Unpack(OwnedCell cell) =>
        throw new InvalidOperationException();

    [Lemma, Requires("OwnerSpec.Held(cell, expected)")]
    [Ensures("OwnerSpec.Raw(cell, Result, Perm.Full)")]
    [Ensures("OwnerSpec.RawValue(Result) == expected")]
    [PulseBody("GhostWitness.unpack_known $(cell) $(expected)")]
    public static Ghost<CellSnapshot> UnpackKnown(OwnedCell cell, int expected) =>
        throw new InvalidOperationException();

    [Lemma, Requires("OwnerSpec.Holds(cell, expected, permission)")]
    [Ensures("OwnerSpec.Raw(cell, Result, permission)")]
    [Ensures("OwnerSpec.RawValue(Result) == expected")]
    [PulseBody("GhostWitness.unpack_fraction $(cell) $(expected) $(permission)")]
    public static Ghost<CellSnapshot> UnpackFraction(OwnedCell cell, int expected, Ghost<Perm> permission) =>
        throw new InvalidOperationException();

    [Lemma, Conditional("PAL")]
    [Requires("OwnerSpec.Raw(cell, record, Perm.Full)")]
    [Ensures("OwnerSpec.Cell(cell)")]
    [PulseBody("GhostWitness.pack $(cell) $(record)")]
    public static void Pack(OwnedCell cell, Ghost<CellSnapshot> record) { }

    [Lemma, Conditional("PAL")]
    [Requires("OwnerSpec.Raw(cell, record, permission)")]
    [Requires("OwnerSpec.RawValue(record) == expected")]
    [Ensures("OwnerSpec.Holds(cell, expected, permission)")]
    [PulseBody("GhostWitness.pack_fraction $(cell) $(record) $(expected) $(permission)")]
    public static void PackFraction(OwnedCell cell, Ghost<CellSnapshot> record, int expected, Ghost<Perm> permission) { }
}

public static class WitnessClient
{
    [Requires("OwnerSpec.Held(cell, expected)")]
    [Ensures("OwnerSpec.Cell(cell)")]
    [Ensures("Result == expected")]
    public static int Read(OwnedCell cell, int expected)
    {
        Ghost<CellSnapshot> record = default;
        Pal.Capture(ref record, WitnessProof.UnpackKnown(cell, expected));
        int value = cell.Current;
        Pal.Assert(value == OwnerSpec.RawValue(record.Value));
        WitnessProof.Pack(cell, record);
        return value;
    }

    [GhostArg("Perm permission")]
    [Preserves("OwnerSpec.Holds(cell, expected, permission)")]
    [Ensures("Result == expected")]
    public static int ReadFraction(OwnedCell cell, int expected)
    {
        Ghost<Perm> fraction = default;
        Pal.Capture(ref fraction, Pal.Ghost<Perm>("permission"));
        Ghost<CellSnapshot> record = default;
        Pal.Capture(ref record, WitnessProof.UnpackFraction(cell, expected, fraction));
        int value = cell.Current;
        Pal.Assert(value == OwnerSpec.RawValue(record.Value));
        WitnessProof.PackFraction(cell, record, expected, fraction);
        return value;
    }
}
