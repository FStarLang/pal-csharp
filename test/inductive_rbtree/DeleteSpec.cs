using System;
using System.Collections.Generic;
using PalLang;

namespace PalCSharp.Tests.Inductive;

public static class RbDeleteSpec
{
    [SpecOp("InductiveOrder.removes_exactly")]
    public static bool RemovesExactly<T>(IComparer<T> comparer, SpecTree<(T, bool)> before,
        T key, SpecTree<(T, bool)> after) =>
        throw new InvalidOperationException("Specification only");
}
