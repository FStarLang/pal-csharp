using System;
using System.Diagnostics;
using PalLang;

// The verified core is translated from annotated code only: everything unannotated
// (StoreBackend, the runtime bodies of the handle classes) is ordinary C#.
[assembly: TranslateAnnotatedOnly]
// The specification (pure F*) and the concurrent database model (Pulse).
[assembly: IncludePulseFile("PetStoreModel.fst")]
[assembly: IncludePulseFile("PetStoreDb.fst")]

namespace PetStore.Verified;

// ---------------------------------------------------------------------------------------
// The C# face of the model: PetStoreModel.db and its operations.
// ---------------------------------------------------------------------------------------

/// <summary>A state of the whole database (PetStoreModel.db). Specification only.</summary>
[SpecType("PetStoreModel.db")]
public sealed class DbState
{
    private DbState() { }

    [SpecOp("PetStoreModel.nprod_of")] public SpecInt Nprod => throw new InvalidOperationException();
    [SpecOp("PetStoreModel.next_oid_of")] public SpecInt NextOid => throw new InvalidOperationException();
    [SpecOp("PetStoreModel.stock_of")] public SpecInt Stock(SpecInt p) => throw new InvalidOperationException();
    [SpecOp("PetStoreModel.received_of")] public SpecInt Received(SpecInt p) => throw new InvalidOperationException();
    [SpecOp("PetStoreModel.cart_of")] public SpecInt Cart(SpecInt c, SpecInt p) => throw new InvalidOperationException();
    [SpecOp("PetStoreModel.is_product")] public bool IsProduct(SpecInt p) => throw new InvalidOperationException();
    [SpecOp("PetStoreModel.any_upto")] public bool AnyUpTo(SpecInt c, SpecInt k) => throw new InvalidOperationException();
    [SpecOp("PetStoreModel.stocked_upto")] public bool StockedUpTo(SpecInt c, SpecInt k) => throw new InvalidOperationException();

    [SpecOp("PetStoreModel.set_stock")]
    public static DbState SetStock(DbState d, SpecInt p, SpecInt v) => throw new InvalidOperationException();
    [SpecOp("PetStoreModel.set_received")]
    public static DbState SetReceived(DbState d, SpecInt p, SpecInt v) => throw new InvalidOperationException();
    [SpecOp("PetStoreModel.set_cart")]
    public static DbState SetCart(DbState d, SpecInt c, SpecInt p, SpecInt q) => throw new InvalidOperationException();
    [SpecOp("PetStoreModel.clear_cart")]
    public static DbState ClearCart(DbState d, SpecInt c) => throw new InvalidOperationException();
    [SpecOp("PetStoreModel.add_order")]
    public static DbState AddOrder(DbState d, SpecInt c) => throw new InvalidOperationException();
    [SpecOp("PetStoreModel.take_upto")]
    public static DbState TakeUpTo(DbState d, SpecInt c, SpecInt k) => throw new InvalidOperationException();
}

/// <summary>The relations of PetStoreModel: the invariant and the three business steps.</summary>
public static class Model
{
    public const int MaxCartQty = 99;

    [Spec, PulseBody("PetStoreModel.inv $(d)")]
    public static bool Inv(DbState d) => throw new InvalidOperationException();

    [Spec, PulseBody("PetStoreModel.fillable $(d) $(c)")]
    public static bool Fillable(DbState d, SpecInt c) => throw new InvalidOperationException();

    [Spec, PulseBody("PetStoreModel.ids_left $(d)")]
    public static bool IdsLeft(DbState d) => throw new InvalidOperationException();

    [Spec, PulseBody("PetStoreModel.cart_updated $(d0) $(d1) $(c) $(p) $(q)")]
    public static bool CartUpdated(DbState d0, DbState d1, SpecInt c, SpecInt p, SpecInt q)
        => throw new InvalidOperationException();

    [Spec, PulseBody("PetStoreModel.restocked $(d0) $(d1) $(p) $(n)")]
    public static bool Restocked(DbState d0, DbState d1, SpecInt p, SpecInt n)
        => throw new InvalidOperationException();

    [Spec, PulseBody("PetStoreModel.order_placed $(d0) $(d1) $(c) $(oid)")]
    public static bool OrderPlaced(DbState d0, DbState d1, SpecInt c, SpecInt oid)
        => throw new InvalidOperationException();
}

/// <summary>Proof steps, proved in PetStoreModel.fst and erased at run time.</summary>
public static class ModelLemmas
{
    [Lemma, Conditional("PAL")]
    [PulseBody("PetStoreModel.stock_le_received $(d) (I32.v $(p))")]
    [Requires("Model.Inv(d)")]
    [Ensures("0 <= d.Stock(p) && d.Stock(p) <= d.Received(p)")]
    public static void StockLeReceived(DbState d, int p) { }

    [Lemma, Conditional("PAL")]
    [PulseBody("PetStoreModel.cart_bounded $(d) (I32.v $(c)) (I32.v $(p))")]
    [Requires("Model.Inv(d)")]
    [Ensures("0 <= d.Cart(c, p) && d.Cart(c, p) <= Model.MaxCartQty")]
    public static void CartBounded(DbState d, int c, int p) { }

    [Lemma, Conditional("PAL")]
    [PulseBody("PetStoreModel.fillable_iff $(d) (I32.v $(c))")]
    [Requires("Model.Inv(d)")]
    [Ensures("Pal.Iff(Model.Fillable(d, c), d.AnyUpTo(c, d.Nprod + 1) && d.StockedUpTo(c, d.Nprod + 1))")]
    public static void FillableIff(DbState d, int c) { }

    [Lemma, Conditional("PAL")]
    [PulseBody("PetStoreModel.stocked_at $(d) (I32.v $(c)) $(k) (I32.v $(p))")]
    [Requires("d.StockedUpTo(c, k) && 1 <= p && p < k")]
    [Ensures("d.Cart(c, p) <= d.Stock(p)")]
    public static void StockedAt(DbState d, int c, SpecInt k, int p) { }

    [Lemma, Conditional("PAL")]
    [PulseBody("PetStoreModel.checkout_placed $(d) (I32.v $(c))")]
    [Requires("Model.Inv(d) && Model.Fillable(d, c) && Model.IdsLeft(d)")]
    [Ensures("Model.OrderPlaced(d, DbState.ClearCart(DbState.AddOrder(DbState.TakeUpTo(d, c, d.Nprod + 1), c), c), c, d.NextOid)")]
    public static void CheckoutPlaced(DbState d, int c) { }
}

// ---------------------------------------------------------------------------------------
// Handles. Each is a real object at run time and an F* value in the proof.
// ---------------------------------------------------------------------------------------

/// <summary>The shared store (PetStoreDb.store): one per process, used by every request.</summary>
[SpecType("PetStoreDb.store")]
public sealed class Store
{
    internal readonly StoreBackend Backend;
    public Store(StoreBackend backend) { Backend = backend; }
}

/// <summary>An open transaction (PetStoreDb.tx), which remembers the state it began in.</summary>
[SpecType("PetStoreDb.tx")]
public sealed class Tx
{
    internal readonly object Handle;
    internal Tx(object handle) { Handle = handle; }

    [SpecOp("PetStoreDb.tx_start")] public DbState Start => throw new InvalidOperationException();
}

/// <summary>
/// What a transaction published (PetStoreDb.receipt): the state it began in, the state it
/// left, and the id of the order it accepted, or 0.
/// </summary>
[SpecType("PetStoreDb.receipt")]
public sealed class Receipt
{
    private readonly int orderId;
    internal Receipt(int orderId) { this.orderId = orderId; }

    [SpecOp("PetStoreDb.receipt_order_id")] public int OrderId => orderId;
    [SpecOp("PetStoreDb.receipt_before")] public DbState Before => throw new InvalidOperationException();
    [SpecOp("PetStoreDb.receipt_after")] public DbState After => throw new InvalidOperationException();
}

// ---------------------------------------------------------------------------------------
// The binders: one SQL statement each. Each is [Implements] a verified function of
// PetStoreDb.fst: its translation is a call to that function, so its contract here is
// *checked* against the model. What is trusted is that the SQL does what the model does.
// ---------------------------------------------------------------------------------------

public static class Db
{
    /// <summary>A client's share of the store (PetStoreDb.live).</summary>
    [SpecOp("PetStoreDb.live")]
    public static SlProp Live(Store s) => throw new InvalidOperationException();

    /// <summary>Transaction <paramref name="t"/> is open on <paramref name="s"/> and sees <paramref name="cur"/>.</summary>
    [SpecOp("PetStoreDb.open_tx")]
    public static SlProp Open(Store s, Tx t, DbState cur) => throw new InvalidOperationException();

    /// <summary>Both states of <paramref name="r"/> are in <paramref name="s"/>'s history, in order.</summary>
    [SpecOp("PetStoreDb.witnessed")]
    public static SlProp Witnessed(Store s, Receipt r) => throw new InvalidOperationException();
}

/// <summary>
/// The binders: one SQL statement each. The translation of each is the call in its
/// <c>[Implements]</c>, to a function of PetStoreDb.fst verified over the model, and its
/// contract is checked against that function's. Its C# body (the SQL) is trusted to
/// behave as the model function does.
/// </summary>
public static class Sql
{
    // -- transactions -------------------------------------------------------------------

    /// <summary>PetStoreDb.begin_tx: SQLite <c>BEGIN IMMEDIATE</c>.</summary>
    [Implements("PetStoreDb.begin_tx $(s)")]
    [Preserves("Db.Live(s)")]
    [Ensures("Db.Open(s, Result, Result.Start)")]
    [Ensures("Model.Inv(Result.Start)")]
    public static Tx Begin(Store s) => new Tx(s.Backend.BeginImmediate());

    /// <summary>PetStoreDb.rollback.</summary>
    [Implements("PetStoreDb.rollback $(s) $(t)")]
    [Preserves("Db.Live(s)")]
    [Requires("Db.Open(s, t, cur)")]
    [Ensures("Db.Witnessed(s, Result)")]
    [Ensures("Pal.Same(Result.Before, t.Start) && Pal.Same(Result.After, t.Start) && Result.OrderId == 0")]
    public static Receipt Rollback(Store s, Tx t, Ghost<DbState> cur = default)
    {
        s.Backend.Rollback(t.Handle);
        return new Receipt(0);
    }

    /// <summary>PetStoreDb.commit_cart.</summary>
    [Implements("PetStoreDb.commit_cart $(s) $(t) $(c) $(p) $(q)")]
    [Preserves("Db.Live(s)")]
    [Requires("Db.Open(s, t, cur)")]
    [Requires("Model.CartUpdated(t.Start, cur, c, p, q)")]
    [Ensures("Db.Witnessed(s, Result)")]
    [Ensures("Pal.Same(Result.Before, t.Start) && Pal.Same(Result.After, cur) && Result.OrderId == 0")]
    public static Receipt CommitCart(Store s, Tx t, int c, int p, int q, Ghost<DbState> cur = default)
    {
        s.Backend.Commit(t.Handle);
        return new Receipt(0);
    }

    /// <summary>PetStoreDb.commit_restock.</summary>
    [Implements("PetStoreDb.commit_restock $(s) $(t) $(p) $(n)")]
    [Preserves("Db.Live(s)")]
    [Requires("Db.Open(s, t, cur)")]
    [Requires("Model.Restocked(t.Start, cur, p, n)")]
    [Ensures("Db.Witnessed(s, Result)")]
    [Ensures("Pal.Same(Result.Before, t.Start) && Pal.Same(Result.After, cur) && Result.OrderId == 0")]
    public static Receipt CommitRestock(Store s, Tx t, int p, int n, Ghost<DbState> cur = default)
    {
        s.Backend.Commit(t.Handle);
        return new Receipt(0);
    }

    /// <summary>PetStoreDb.commit_order.</summary>
    [Implements("PetStoreDb.commit_order $(s) $(t) $(c) $(oid)")]
    [Preserves("Db.Live(s)")]
    [Requires("Db.Open(s, t, cur)")]
    [Requires("Model.OrderPlaced(t.Start, cur, c, oid)")]
    [Ensures("Db.Witnessed(s, Result)")]
    [Ensures("Pal.Same(Result.Before, t.Start) && Pal.Same(Result.After, cur) && Result.OrderId == (SpecInt)oid")]
    public static Receipt CommitOrder(Store s, Tx t, int c, int oid, Ghost<DbState> cur = default)
    {
        s.Backend.Commit(t.Handle);
        return new Receipt(oid);
    }

    // -- reads ---------------------------------------------------------------------------

    /// <summary>PetStoreDb.get_nprod: <c>SELECT COUNT(*) FROM products</c>.</summary>
    [Implements("PetStoreDb.get_nprod $(s) $(t)")]
    [Preserves("Db.Open(s, t, cur)")]
    [Ensures("Result == cur.Nprod")]
    public static int ProductCount(Store s, Tx t, Ghost<DbState> cur = default)
        => s.Backend.ProductCount(t.Handle);

    /// <summary>PetStoreDb.get_stock.</summary>
    [Implements("PetStoreDb.get_stock $(s) $(t) $(p)")]
    [Preserves("Db.Open(s, t, cur)")]
    [Ensures("Result == cur.Stock(p)")]
    public static int Stock(Store s, Tx t, int p, Ghost<DbState> cur = default)
        => s.Backend.Stock(t.Handle, p);

    /// <summary>PetStoreDb.get_received.</summary>
    [Implements("PetStoreDb.get_received $(s) $(t) $(p)")]
    [Preserves("Db.Open(s, t, cur)")]
    [Ensures("Result == cur.Received(p)")]
    public static int Received(Store s, Tx t, int p, Ghost<DbState> cur = default)
        => s.Backend.Received(t.Handle, p);

    /// <summary>PetStoreDb.get_cart.</summary>
    [Implements("PetStoreDb.get_cart $(s) $(t) $(c) $(p)")]
    [Preserves("Db.Open(s, t, cur)")]
    [Ensures("Result == cur.Cart(c, p)")]
    public static int CartQty(Store s, Tx t, int c, int p, Ghost<DbState> cur = default)
        => s.Backend.CartQty(t.Handle, c, p);

    /// <summary>PetStoreDb.get_next_oid.</summary>
    [Implements("PetStoreDb.get_next_oid $(s) $(t)")]
    [Preserves("Db.Open(s, t, cur)")]
    [Ensures("Result == cur.NextOid")]
    public static int NextOrderId(Store s, Tx t, Ghost<DbState> cur = default)
        => s.Backend.NextOrderId(t.Handle);

    // -- writes --------------------------------------------------------------------------

    /// <summary>PetStoreDb.write_stock.</summary>
    [Implements("PetStoreDb.write_stock $(s) $(t) $(p) $(v)")]
    [Requires("Db.Open(s, t, cur)")]
    [Requires("0 <= v")]
    [Ensures("Db.Open(s, t, DbState.SetStock(cur, p, v))")]
    public static void SetStock(Store s, Tx t, int p, int v, Ghost<DbState> cur = default)
        => s.Backend.SetStock(t.Handle, p, v);

    /// <summary>PetStoreDb.write_received.</summary>
    [Implements("PetStoreDb.write_received $(s) $(t) $(p) $(v)")]
    [Requires("Db.Open(s, t, cur)")]
    [Requires("0 <= v")]
    [Ensures("Db.Open(s, t, DbState.SetReceived(cur, p, v))")]
    public static void SetReceived(Store s, Tx t, int p, int v, Ghost<DbState> cur = default)
        => s.Backend.SetReceived(t.Handle, p, v);

    /// <summary>PetStoreDb.write_cart.</summary>
    [Implements("PetStoreDb.write_cart $(s) $(t) $(c) $(p) $(q)")]
    [Requires("Db.Open(s, t, cur)")]
    [Requires("0 <= q && q <= Model.MaxCartQty")]
    [Ensures("Db.Open(s, t, DbState.SetCart(cur, c, p, q))")]
    public static void SetCartQty(Store s, Tx t, int c, int p, int q, Ghost<DbState> cur = default)
        => s.Backend.SetCartQty(t.Handle, c, p, q);

    /// <summary>PetStoreDb.write_clear_cart.</summary>
    [Implements("PetStoreDb.write_clear_cart $(s) $(t) $(c)")]
    [Requires("Db.Open(s, t, cur)")]
    [Ensures("Db.Open(s, t, DbState.ClearCart(cur, c))")]
    public static void ClearCart(Store s, Tx t, int c, Ghost<DbState> cur = default)
        => s.Backend.ClearCart(t.Handle, c);

    /// <summary>PetStoreDb.insert_order: the order's lines are the customer's cart.</summary>
    [Implements("PetStoreDb.insert_order $(s) $(t) $(c)")]
    [Requires("Db.Open(s, t, cur)")]
    [Requires("Model.IdsLeft(cur)")]
    [Ensures("Db.Open(s, t, DbState.AddOrder(cur, c))")]
    public static void InsertOrder(Store s, Tx t, int c, Ghost<DbState> cur = default)
        => s.Backend.InsertOrderFromCart(t.Handle, s.Backend.NextOrderId(t.Handle), c);
}
