using Microsoft.Data.Sqlite;
using PetStore.Verified;

namespace PetStore.Web.Data;

/// <summary>
/// The SQL behind the verified binders (PetStore.Verified.Sql): one statement per method,
/// each run inside the transaction it is handed. This class is trusted: its methods must
/// do what the binders' contracts (and the functions of the same name in PetStoreDb.fst)
/// say they do.
/// </summary>
public sealed class SqliteBackend : StoreBackend
{
    private readonly string connectionString;

    // The transaction this logical request has open, if any, so that a request that dies
    // halfway (an exception thrown by SQLite, say) can release the database.
    private readonly AsyncLocal<SqliteTx?> current = new();

    public SqliteBackend(string connectionString) { this.connectionString = connectionString; }

    private sealed class SqliteTx(SqliteConnection conn, SqliteTransaction tx)
    {
        public readonly SqliteConnection Conn = conn;
        public readonly SqliteTransaction Tx = tx;
    }

    /// <summary>
    /// BEGIN IMMEDIATE takes SQLite's write lock up front, so transactions are serialized
    /// exactly as the model's lock serializes them (PetStoreDb.begin_tx). Blocks, with
    /// SQLite's busy timeout, while another transaction holds the lock.
    /// </summary>
    public override object BeginImmediate()
    {
        var conn = new SqliteConnection(connectionString);
        conn.Open();
        var tx = conn.BeginTransaction(deferred: false);
        var t = new SqliteTx(conn, tx);
        current.Value = t;
        return t;
    }

    public override void Commit(object tx) => End(tx, commit: true);
    public override void Rollback(object tx) => End(tx, commit: false);

    private void End(object tx, bool commit)
    {
        var t = (SqliteTx)tx;
        if (commit) t.Tx.Commit(); else t.Tx.Rollback();
        t.Tx.Dispose();
        t.Conn.Dispose();
        if (ReferenceEquals(current.Value, t)) current.Value = null;
    }

    /// <summary>Roll back whatever transaction this request left open.</summary>
    public void AbortCurrent()
    {
        var t = current.Value;
        if (t is null) return;
        current.Value = null;
        try { t.Tx.Rollback(); } catch (Exception) { /* already finished or broken */ }
        t.Tx.Dispose();
        t.Conn.Dispose();
    }

    private static SqliteCommand Cmd(object tx, string sql, params (string, object)[] args)
    {
        var t = (SqliteTx)tx;
        var cmd = t.Conn.CreateCommand();
        cmd.Transaction = t.Tx;
        cmd.CommandText = sql;
        foreach (var (name, value) in args) cmd.Parameters.AddWithValue(name, value);
        return cmd;
    }

    private static int Scalar(object tx, string sql, params (string, object)[] args)
    {
        using var cmd = Cmd(tx, sql, args);
        return Convert.ToInt32(cmd.ExecuteScalar() ?? 0);
    }

    private static void Exec(object tx, string sql, params (string, object)[] args)
    {
        using var cmd = Cmd(tx, sql, args);
        cmd.ExecuteNonQuery();
    }

    public override int ProductCount(object tx) =>
        Scalar(tx, "SELECT COUNT(*) FROM products");

    public override int Stock(object tx, int product) =>
        Scalar(tx, "SELECT COALESCE((SELECT stock FROM products WHERE id = $p), 0)", ("$p", product));

    public override int Received(object tx, int product) =>
        Scalar(tx, "SELECT COALESCE((SELECT received FROM products WHERE id = $p), 0)", ("$p", product));

    public override int CartQty(object tx, int customer, int product) =>
        Scalar(tx, "SELECT COALESCE((SELECT qty FROM cart_items WHERE customer = $c AND product = $p), 0)",
               ("$c", customer), ("$p", product));

    public override int NextOrderId(object tx) =>
        Scalar(tx, "SELECT COALESCE(MAX(id), 0) + 1 FROM orders");

    public override void SetStock(object tx, int product, int value) =>
        Exec(tx, "UPDATE products SET stock = $v WHERE id = $p", ("$v", value), ("$p", product));

    public override void SetReceived(object tx, int product, int value) =>
        Exec(tx, "UPDATE products SET received = $v WHERE id = $p", ("$v", value), ("$p", product));

    public override void SetCartQty(object tx, int customer, int product, int qty)
    {
        if (qty == 0)
            Exec(tx, "DELETE FROM cart_items WHERE customer = $c AND product = $p",
                 ("$c", customer), ("$p", product));
        else
            Exec(tx, "INSERT INTO cart_items (customer, product, qty) VALUES ($c, $p, $q) " +
                     "ON CONFLICT (customer, product) DO UPDATE SET qty = excluded.qty",
                 ("$c", customer), ("$p", product), ("$q", qty));
    }

    public override void ClearCart(object tx, int customer) =>
        Exec(tx, "DELETE FROM cart_items WHERE customer = $c", ("$c", customer));

    public override void InsertOrderFromCart(object tx, int orderId, int customer)
    {
        Exec(tx, "INSERT INTO orders (id, customer, placed_at) VALUES ($o, $c, $t)",
             ("$o", orderId), ("$c", customer), ("$t", DateTime.UtcNow.ToString("u")));
        Exec(tx, "INSERT INTO order_items (order_id, product, qty, price_cents) " +
                 "SELECT $o, ci.product, ci.qty, p.price_cents " +
                 "FROM cart_items ci JOIN products p ON p.id = ci.product " +
                 "WHERE ci.customer = $c AND ci.qty > 0",
             ("$o", orderId), ("$c", customer));
    }
}
