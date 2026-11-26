using System.Reflection;
using System.Text.Json;
using Xunit;

if (typeof(SortedSet<int>).Assembly != Assembly.GetExecutingAssembly())
    throw new InvalidOperationException("The repro is using the installed BCL, not the pinned sources.");

int passed = 0;
int failed = 0;
var regression = new ViewRangeRegression();
foreach (MethodInfo method in typeof(ViewRangeRegression).GetMethods()
    .Where(m => m.GetCustomAttribute<TheoryAttribute>() is not null))
{
    foreach (InlineDataAttribute row in method.GetCustomAttributes<InlineDataAttribute>())
    {
        string name = $"{method.Name}({string.Join(", ", row.Arguments)})";
        try
        {
            method.Invoke(regression, row.Arguments);
            Console.WriteLine($"PASS {name}");
            passed++;
        }
        catch (TargetInvocationException error) when (error.InnerException is AssertionFailure)
        {
            Console.WriteLine($"FAIL {name}: {error.InnerException.Message}");
            failed++;
        }
    }
}

var set = new SortedSet<int>();
for (int i = 0; i < 10; i++)
    set.Add(i);
SortedSet<int> view = set.GetViewBetween(2, 5);
var observations = new Dictionary<string, bool>
{
    ["SetEquals"] = view.SetEquals(new List<int> { 2, 3, 4, 9 }),
    ["IsSubsetOf"] = view.IsSubsetOf(new List<int> { 2, 3, 4, 9 }),
    ["IsProperSubsetOf"] = view.IsProperSubsetOf(new List<int> { 2, 3, 4, 9, 10 }),
    ["IsProperSupersetOf"] = view.IsProperSupersetOf(new List<int> { 2, 3, 9 }),
};
Console.WriteLine($"View: {{{string.Join(", ", view)}}}; expected all four results below to be false.");

// Inspect the actual source-defined methods; these observations do not change the tree.
MethodInfo indexOf = typeof(SortedSet<int>).GetMethod("InternalIndexOf", BindingFlags.Instance | BindingFlags.NonPublic)!;
MethodInfo height = typeof(SortedSet<int>).GetMethod("GetApproximateMaxHeight", BindingFlags.Instance | BindingFlags.NonPublic)!;
Console.WriteLine($"Raw subtree index of 9: {indexOf.Invoke(view, [9])}; view.Contains(9): {view.Contains(9)}; height bound: {height.Invoke(view, null)}");

int controls = 0;
CheckRelations("inclusive endpoints and duplicates", view, [2, 3, 4, 5, 2, 5]);
CheckRelations("absent from underlying set", view, [99]);
CheckRelations("empty view", set.GetViewBetween(20, 30), []);
var originalIssue = new SortedSet<int>();
for (int i = 0; i < 18; i++)
    originalIssue.Add(i);
CheckRelations("original duplicate-count regression", originalIssue,
    Enumerable.Range(0, 18).Concat(Enumerable.Range(0, 18)).ToArray());
var large = new SortedSet<int>();
for (int i = 0; i < 130; i++)
    large.Add(i);
SortedSet<int> largeView = large.GetViewBetween(20, 100);
_ = largeView.Count;
int fallbackHeight = (int)height.Invoke(largeView, null)!;
if (fallbackHeight <= 12)
    throw new InvalidOperationException("The fallback control did not reach the fallback threshold.");
CheckRelations("existing fallback path", largeView, [20, 21, 129]);
Console.WriteLine($"Fallback control height bound: {fallbackHeight}");

var edgeFailures = new List<string>();
CheckEdge("outside-first-with-duplicates", view, [9, 2, 3, 4, 5, 9]);
var descending = new SortedSet<int>(Comparer<int>.Create((x, y) => y.CompareTo(x)));
for (int i = 0; i < 10; i++)
    descending.Add(i);
CheckEdge("descending-comparer", descending.GetViewBetween(5, 2), [2, 3, 4, 9]);
var ignoreCase = new SortedSet<string>(StringComparer.OrdinalIgnoreCase);
foreach (char item in "abcdefghij")
    ignoreCase.Add(item.ToString());
CheckEdge("case-insensitive-comparer", ignoreCase.GetViewBetween("c", "f"),
    ["C", "D", "E", "J"], StringComparer.OrdinalIgnoreCase);

Console.WriteLine("RESULT " + JsonSerializer.Serialize(new { passed, failed, controls, observations, edgeFailures }));
return failed == 0 && edgeFailures.Count == 0 ? 0 : 1;

void CheckRelations(string name, SortedSet<int> subject, int[] other)
{
    var expected = new HashSet<int>(subject);
    bool[] actual = [subject.SetEquals(other), subject.IsSubsetOf(other),
        subject.IsProperSubsetOf(other), subject.IsProperSupersetOf(other)];
    bool[] oracle = [expected.SetEquals(other), expected.IsSubsetOf(other),
        expected.IsProperSubsetOf(other), expected.IsProperSupersetOf(other)];
    if (!actual.SequenceEqual(oracle))
        throw new InvalidOperationException($"Unexpected control failure: {name}");
    controls += actual.Length;
    Console.WriteLine($"PASS control: {name}");
}

void CheckEdge<T>(string name, SortedSet<T> subject, T[] other, IEqualityComparer<T>? equality = null)
{
    var expected = new HashSet<T>(subject, equality);
    string[] methods = ["SetEquals", "IsSubsetOf", "IsProperSubsetOf", "IsProperSupersetOf"];
    bool[] actual = [subject.SetEquals(other), subject.IsSubsetOf(other),
        subject.IsProperSubsetOf(other), subject.IsProperSupersetOf(other)];
    bool[] oracle = [expected.SetEquals(other), expected.IsSubsetOf(other),
        expected.IsProperSubsetOf(other), expected.IsProperSupersetOf(other)];
    for (int i = 0; i < methods.Length; i++)
    {
        string label = $"{name}/{methods[i]}";
        if (actual[i] != oracle[i])
        {
            edgeFailures.Add(label);
            Console.WriteLine($"FAIL {label}: expected {oracle[i]}, got {actual[i]}");
        }
        else
        {
            Console.WriteLine($"PASS {label}");
        }
    }
}
