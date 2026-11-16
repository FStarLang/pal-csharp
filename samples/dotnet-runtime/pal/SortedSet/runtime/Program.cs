extern alias subject;

using ActualSet = subject::System.Collections.Generic.SortedSet<int>;
using ActualDictionary = subject::System.Collections.Generic.SortedDictionary<int, string>;

static void Check(bool condition)
{
    if (!condition) throw new Exception("Ghost erasure changed collection behavior");
}

static void Same(ActualSet actual, SortedSet<int> expected)
{
    Check(actual.Count == expected.Count && actual.SequenceEqual(expected));
    Check(actual.Reverse().SequenceEqual(expected.Reverse()));
    var copy = new int[actual.Count + 2];
    actual.CopyTo(copy, 1);
    Check(copy.Skip(1).Take(actual.Count).SequenceEqual(expected));
}

foreach (var comparer in new[]
{
    Comparer<int>.Default,
    Comparer<int>.Create((x, y) => y.CompareTo(x)),
})
{
    var actual = new ActualSet(Enumerable.Range(1, 31), comparer);
    var expected = new SortedSet<int>(Enumerable.Range(1, 31), comparer);
    actual.UnionWith(Enumerable.Range(32, 64));
    expected.UnionWith(Enumerable.Range(32, 64));
    Same(actual, expected);
    var clone = new ActualSet(actual, comparer);
    Same(clone, expected);
    foreach (var key in Enumerable.Range(1, 96))
        Check(clone.Remove(key) == expected.Remove(key));
    Same(clone, expected);
    expected = new SortedSet<int>(actual, comparer);
    var all = expected.ToArray();
    Check(actual.IsSubsetOf(all) && actual.SetEquals(all));
    Check(actual.Overlaps(all) && !actual.Overlaps(new[] { -1, -2 }));
    actual.IntersectWith(new ActualSet(Enumerable.Range(16, 31), comparer));
    expected.IntersectWith(new SortedSet<int>(Enumerable.Range(16, 31), comparer));
    Same(actual, expected);
    int lo = comparer.Compare(20, 30) < 0 ? 20 : 30;
    int hi = lo == 20 ? 30 : 20;
    var view = actual.GetViewBetween(lo, hi);
    var referenceView = expected.GetViewBetween(lo, hi);
    Same(view, referenceView);
    Check(view.RemoveWhere(x => x % 2 == 0) == referenceView.RemoveWhere(x => x % 2 == 0));
    Same(actual, expected);
    view.Clear();
    referenceView.Clear();
    Same(actual, expected);

    var dictionary = new ActualDictionary(comparer);
    var reference = new SortedDictionary<int, string>(comparer);
    for (int key = 0; key < 32; key++)
    {
        dictionary.Add(key, key.ToString());
        reference.Add(key, key.ToString());
        dictionary[key] = "replaced";
        reference[key] = "replaced";
    }
    Check(dictionary.SequenceEqual(reference));
    Check(dictionary.Keys.SequenceEqual(reference.Keys));
    Check(dictionary.Values.SequenceEqual(reference.Values));
}

var fields = typeof(ActualSet).GetFields(System.Reflection.BindingFlags.Instance |
    System.Reflection.BindingFlags.DeclaredOnly | System.Reflection.BindingFlags.NonPublic |
    System.Reflection.BindingFlags.Public);
Check(fields.Select(f => f.Name).Order().SequenceEqual(new[] { "comparer", "count", "root", "siInfo", "version" }));
Check(typeof(ActualSet).GetMethod("ReplaceChildOrRoot",
    System.Reflection.BindingFlags.Instance | System.Reflection.BindingFlags.NonPublic)!.GetParameters().Length == 3);
Console.WriteLine("Shared SortedSet source: stock runtime ghost erasure and collection behavior passed.");
