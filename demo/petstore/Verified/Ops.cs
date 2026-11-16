using PalLang;

namespace PetStore.Verified;

/// <summary>The store's business operations, verified against PetStoreModel.</summary>
public sealed class Ops
{
    // A readonly field: bound once, as an immutable parameter of each method's proof.
    private readonly Store s;

    public Ops(Store store) { s = store; }

    [Requires("Db.Live(s)")]
    [Ensures("Db.Live(s)")]
    [Ensures("Db.Witnessed(s, Result)")]
    [Ensures("Result.OrderId == 0")]
    [Ensures("Pal.Implies(Result.Before.IsProduct(p) && 0 < n && Result.Before.Received(p) + n <= 2147483647, " +
             "Model.Restocked(Result.Before, Result.After, p, n))")]
    [Ensures("Pal.Implies(!(Result.Before.IsProduct(p) && 0 < n && Result.Before.Received(p) + n <= 2147483647), " +
             "Pal.Same(Result.After, Result.Before))")]
    public Receipt Restock(int p, int n)
    {
        Tx t = Sql.Begin(s);
        int count = Sql.ProductCount(s, t);
        if (p < 1 || p > count || n <= 0)
        {
            return Sql.Rollback(s, t);
        }
        int received = Sql.Received(s, t, p);
        if (received > int.MaxValue - n)
        {
            return Sql.Rollback(s, t);
        }
        int stock = Sql.Stock(s, t, p);
        ModelLemmas.StockLeReceived(t.Start, p);
        Sql.SetStock(s, t, p, stock + n);
        Sql.SetReceived(s, t, p, received + n);
        return Sql.CommitRestock(s, t, p, n);
    }

    /// <summary>Set the quantity of product <paramref name="p"/> in customer <paramref name="c"/>'s cart.</summary>
    [Requires("Db.Live(s)")]
    [Ensures("Db.Live(s)")]
    [Ensures("Db.Witnessed(s, Result)")]
    [Ensures("Result.OrderId == 0")]
    [Ensures("Pal.Implies(Result.Before.IsProduct(p) && 0 <= q && q <= Model.MaxCartQty, " +
             "Model.CartUpdated(Result.Before, Result.After, c, p, q))")]
    [Ensures("Pal.Implies(!(Result.Before.IsProduct(p) && 0 <= q && q <= Model.MaxCartQty), " +
             "Pal.Same(Result.After, Result.Before))")]
    public Receipt SetCartQty(int c, int p, int q)
    {
        Tx t = Sql.Begin(s);
        int count = Sql.ProductCount(s, t);
        if (p < 1 || p > count || q < 0 || q > Model.MaxCartQty)
        {
            return Sql.Rollback(s, t);
        }
        Sql.SetCartQty(s, t, c, p, q);
        return Sql.CommitCart(s, t, c, p, q);
    }

    /// <summary>Add <paramref name="n"/> more units of <paramref name="p"/> to <paramref name="c"/>'s cart.</summary>
    [Requires("Db.Live(s)")]
    [Ensures("Db.Live(s)")]
    [Ensures("Db.Witnessed(s, Result)")]
    [Ensures("Result.OrderId == 0")]
    [Ensures("Pal.Implies(Result.Before.IsProduct(p) && 0 < n && Result.Before.Cart(c, p) + n <= Model.MaxCartQty, " +
             "Model.CartUpdated(Result.Before, Result.After, c, p, Result.Before.Cart(c, p) + n))")]
    [Ensures("Pal.Implies(!(Result.Before.IsProduct(p) && 0 < n && Result.Before.Cart(c, p) + n <= Model.MaxCartQty), " +
             "Pal.Same(Result.After, Result.Before))")]
    public Receipt AddToCart(int c, int p, int n)
    {
        Tx t = Sql.Begin(s);
        int count = Sql.ProductCount(s, t);
        ModelLemmas.CartBounded(t.Start, c, p);
        if (p < 1 || p > count || n <= 0 || n > Model.MaxCartQty)
        {
            return Sql.Rollback(s, t);
        }
        int have = Sql.CartQty(s, t, c, p);
        if (have > Model.MaxCartQty - n)
        {
            return Sql.Rollback(s, t);
        }
        Sql.SetCartQty(s, t, c, p, have + n);
        return Sql.CommitCart(s, t, c, p, have + n);
    }

    /// <summary>
    /// Check out customer <paramref name="c"/>'s cart: accept it as an order exactly when
    /// the store has every unit it asks for, take those units off the shelf, and empty the
    /// cart. All of it is one transaction, so it is atomic with respect to every other
    /// client.
    /// </summary>
    [Requires("Db.Live(s)")]
    [Ensures("Db.Live(s)")]
    [Ensures("Db.Witnessed(s, Result)")]
    [Ensures("Pal.Implies(Model.Fillable(Result.Before, c) && Model.IdsLeft(Result.Before), " +
             "Result.OrderId == Result.Before.NextOid && " +
             "Model.OrderPlaced(Result.Before, Result.After, c, Result.OrderId))")]
    [Ensures("Pal.Implies(!(Model.Fillable(Result.Before, c) && Model.IdsLeft(Result.Before)), " +
             "Result.OrderId == 0 && Pal.Same(Result.After, Result.Before))")]
    public Receipt PlaceOrder(int c)
    {
        Tx t = Sql.Begin(s);
        int count = Sql.ProductCount(s, t);

        // Scan the cart: is anything in it, and is all of it on the shelf?
        bool any = false;
        bool ok = true;
        int p = 1;
        while (p <= count)
        {
            Pal.Invariant(c == Pal.Old(c));
            Pal.Invariant(Db.Live(s));
            Pal.Invariant(Db.Open(s, t, t.Start));
            Pal.Invariant(Model.Inv(t.Start));
            Pal.Invariant(count == t.Start.Nprod);
            Pal.Invariant(1 <= p && p <= count + 1);
            Pal.Invariant(Pal.Iff(any, t.Start.AnyUpTo(c, p)));
            Pal.Invariant(Pal.Iff(ok, t.Start.StockedUpTo(c, p)));
            Pal.Decreases(count + 1 - p);
            int want = Sql.CartQty(s, t, c, p);
            int have = Sql.Stock(s, t, p);
            if (want > 0)
            {
                any = true;
            }
            if (want > have)
            {
                ok = false;
            }
            p = p + 1;
        }
        ModelLemmas.FillableIff(t.Start, c);
        if (!any || !ok)
        {
            return Sql.Rollback(s, t);
        }
        int oid = Sql.NextOrderId(s, t);
        if (oid == int.MaxValue)
        {
            return Sql.Rollback(s, t);
        }

        // Take the units off the shelf.
        p = 1;
        while (p <= count)
        {
            Pal.Invariant(c == Pal.Old(c));
            Pal.Invariant(Db.Live(s));
            Pal.Invariant(Db.Open(s, t, DbState.TakeUpTo(t.Start, c, p)));
            Pal.Invariant(Model.Inv(t.Start));
            Pal.Invariant(count == t.Start.Nprod);
            Pal.Invariant(1 <= p && p <= count + 1);
            Pal.Invariant(t.Start.StockedUpTo(c, count + 1));
            Pal.Decreases(count + 1 - p);
            int want = Sql.CartQty(s, t, c, p);
            int have = Sql.Stock(s, t, p);
            if (want > 0)
            {
                ModelLemmas.StockedAt(t.Start, c, count + 1, p);
                Sql.SetStock(s, t, p, have - want);
            }
            p = p + 1;
        }

        // Record the order, with the cart's lines, and empty the cart.
        Sql.InsertOrder(s, t, c);
        Sql.ClearCart(s, t, c);
        ModelLemmas.CheckoutPlaced(t.Start, c);
        return Sql.CommitOrder(s, t, c, oid);
    }
}
