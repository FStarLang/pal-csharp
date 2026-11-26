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

// Do not touch Count before enumerating: a view's cached count is not the
// logical length its iterator must describe. This is a concrete witness for
// why the ordinary iterator's count-based specification cannot simply be
// installed as the view's base capability.
var cacheSource = new ActualSet();
for (int key = 0; key < 10; key++) cacheSource.Add(key);
var cacheView = cacheSource.GetViewBetween(2, 5);
var countField = typeof(ActualSet).GetField("count",
    System.Reflection.BindingFlags.Instance | System.Reflection.BindingFlags.NonPublic)!;
int countBefore = (int)countField.GetValue(cacheView)!;
var enumerated = new List<int>();
using (var iterator = cacheView.GetEnumerator())
    while (iterator.MoveNext()) enumerated.Add(iterator.Current);
int countAfter = (int)countField.GetValue(cacheView)!;
Check(countBefore == 0 && countAfter == 0);
Check(enumerated.SequenceEqual(new[] { 2, 3, 4, 5 }));
var enumerationProof = typeof(ActualSet).GetMethod("EnumerationProof",
    System.Reflection.BindingFlags.Instance | System.Reflection.BindingFlags.NonPublic)!;
Check(((IEnumerable<int>)enumerationProof.Invoke(cacheSource, null)!).SequenceEqual(Enumerable.Range(0, 10)));
Check(((IEnumerable<int>)enumerationProof.Invoke(cacheView, null)!).SequenceEqual(new[] { 2, 3, 4, 5 }));
Check(!((IEnumerable<int>)enumerationProof.Invoke(new ActualSet(), null)!).Any());
Check((int)countField.GetValue(cacheView)! == 0);
Console.WriteLine($"View iterator: cached count {countBefore}->{countAfter}, yielded {string.Join(",", enumerated)}");
Check(!cacheView.SetEquals(new List<int> { 2, 3, 4, 9 }));
Check(!cacheView.SetEquals(new ActualSet(new[] { 2, 3, 4, 9 })));
var publicRegression = typeof(ActualSet).Assembly
    .GetType("System.Collections.Generic.SortedSetPublicRegression")!
    .GetMethod("ViewSetEqualsListFalse",
        System.Reflection.BindingFlags.Static | System.Reflection.BindingFlags.NonPublic)!;
Check(!(bool)publicRegression.Invoke(null, null)!);

var largeSet = new ActualSet(Enumerable.Range(0, 256));
var largeView = largeSet.GetViewBetween(0, 255);
Check(largeView.Count == 256);
var maxHeight = typeof(ActualSet).GetMethod("GetApproximateMaxHeight",
    System.Reflection.BindingFlags.Instance | System.Reflection.BindingFlags.NonPublic)!;
Check((int)maxHeight.Invoke(largeSet, null)! > 12 && (int)maxHeight.Invoke(largeView, null)! > 12);
var repeated = Enumerable.Range(0, 256).Concat(new[] { 2, 2, 255 }).ToList();
Check(largeSet.SetEquals(repeated) && largeView.SetEquals(repeated));
Check(!largeView.SetEquals(new List<int> { 2, 3, 4, 4, 5, 300 }));
Check(!largeSet.SetEquals(Array.Empty<int>()));
Check(largeSet.IsSubsetOf(repeated));
Check(largeSet.IsProperSubsetOf(repeated.Append(300)));
Check(largeSet.IsProperSupersetOf(new List<int> { 2, 3, 3, 4 }));
foreach (var (name, expected) in new[]
{
    ("LargeViewSetEqualsListFalse", false),
    ("LargeSetEqualsListTrue", true),
})
{
    var regression = typeof(ActualSet).Assembly
        .GetType("System.Collections.Generic.SortedSetPublicRegression")!
        .GetMethod(name, System.Reflection.BindingFlags.Static | System.Reflection.BindingFlags.NonPublic)!;
    Check((bool)regression.Invoke(null, null)! == expected);
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
