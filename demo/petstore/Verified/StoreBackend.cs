namespace PetStore.Verified;

/// <summary>
/// What a binder in <see cref="Db"/> does at run time: one SQL statement, against the
/// transaction it is given. The SQLite implementation lives in the web project
/// (Web/SqliteBackend.cs). Nothing here is translated or verified; the binders' contracts
/// are what the verified code relies on, and they are trusted to describe these methods.
/// </summary>
public abstract class StoreBackend
{
    public abstract object BeginImmediate();
    public abstract void Commit(object tx);
    public abstract void Rollback(object tx);

    public abstract int ProductCount(object tx);
    public abstract int Stock(object tx, int product);
    public abstract int Received(object tx, int product);
    public abstract int CartQty(object tx, int customer, int product);
    public abstract int NextOrderId(object tx);

    public abstract void SetStock(object tx, int product, int value);
    public abstract void SetReceived(object tx, int product, int value);
    public abstract void SetCartQty(object tx, int customer, int product, int qty);
    public abstract void ClearCart(object tx, int customer);
    public abstract void InsertOrderFromCart(object tx, int orderId, int customer);
}
