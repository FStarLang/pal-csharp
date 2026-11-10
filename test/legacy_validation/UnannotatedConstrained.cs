// An unsupported constraint on unrelated source must not block annotated methods.
public sealed class UnannotatedConstrained<T> where T : struct
{
    public T Value { get; set; }
}
