using Microsoft.Data.Sqlite;

namespace PetStore.Web.Data;

public sealed record Product(int Id, string Name, string Blurb, int PriceCents, int Stock, int Received);
public sealed record CartLine(Product Product, int Qty);
public sealed record OrderLine(int Product, string Name, int Qty, int PriceCents);
public sealed record Order(int Id, int Customer, string PlacedAt, List<OrderLine> Lines)
{
    public int TotalCents => Lines.Sum(l => l.Qty * l.PriceCents);
}
public sealed record AuditRow(int Id, string Name, int Stock, int Received, int Sold)
{
    public bool Ok => Stock >= 0 && Stock + Sold == Received;
}

/// <summary>
/// Read-only queries for display. These are not part of the verified core: every change to
/// the database goes through <see cref="PetStore.Verified.Ops"/>. Each runs as one SELECT
/// (or one read transaction), so it sees a committed state.
/// </summary>
public sealed class Catalog(string connectionString)
{
    private SqliteConnection Open()
    {
        var c = new SqliteConnection(connectionString);
        c.Open();
        return c;
    }

    private static Product ReadProduct(SqliteDataReader r, int at = 0) =>
        new(r.GetInt32(at), r.GetString(at + 1), r.GetString(at + 2), r.GetInt32(at + 3), r.GetInt32(at + 4), r.GetInt32(at + 5));

    private const string ProductCols = "p.id, p.name, p.blurb, p.price_cents, p.stock, p.received";

    public List<Product> Products()
    {
        using var conn = Open();
        using var cmd = conn.CreateCommand();
        cmd.CommandText = $"SELECT {ProductCols} FROM products p ORDER BY p.id";
        using var r = cmd.ExecuteReader();
        var list = new List<Product>();
        while (r.Read()) list.Add(ReadProduct(r));
        return list;
    }

    public List<CartLine> Cart(int customer)
    {
        using var conn = Open();
        using var cmd = conn.CreateCommand();
        cmd.CommandText = $"SELECT {ProductCols}, ci.qty FROM cart_items ci JOIN products p ON p.id = ci.product " +
                          "WHERE ci.customer = $c ORDER BY p.id";
        cmd.Parameters.AddWithValue("$c", customer);
        using var r = cmd.ExecuteReader();
        var list = new List<CartLine>();
        while (r.Read()) list.Add(new CartLine(ReadProduct(r), r.GetInt32(6)));
        return list;
    }

    public List<Order> Orders(int? customer)
    {
        using var conn = Open();
        using var tx = conn.BeginTransaction();
        var orders = new Dictionary<int, Order>();
        using (var cmd = conn.CreateCommand())
        {
            cmd.Transaction = tx;
            cmd.CommandText = "SELECT id, customer, placed_at FROM orders " +
                              (customer is null ? "" : "WHERE customer = $c ") + "ORDER BY id DESC";
            if (customer is not null) cmd.Parameters.AddWithValue("$c", customer);
            using var r = cmd.ExecuteReader();
            while (r.Read()) orders[r.GetInt32(0)] = new Order(r.GetInt32(0), r.GetInt32(1), r.GetString(2), []);
        }
        using (var cmd = conn.CreateCommand())
        {
            cmd.Transaction = tx;
            cmd.CommandText = "SELECT oi.order_id, oi.product, p.name, oi.qty, oi.price_cents " +
                              "FROM order_items oi JOIN products p ON p.id = oi.product ORDER BY oi.order_id, oi.product";
            using var r = cmd.ExecuteReader();
            while (r.Read())
                if (orders.TryGetValue(r.GetInt32(0), out var o))
                    o.Lines.Add(new OrderLine(r.GetInt32(1), r.GetString(2), r.GetInt32(3), r.GetInt32(4)));
        }
        return orders.Values.ToList();
    }

    /// <summary>
    /// The model's conservation invariant, checked against the live tables: for every
    /// product, stock is non-negative and stock + units sold == units received.
    /// </summary>
    public List<AuditRow> Audit()
    {
        using var conn = Open();
        using var cmd = conn.CreateCommand();
        cmd.CommandText = "SELECT p.id, p.name, p.stock, p.received, " +
                          "COALESCE((SELECT SUM(qty) FROM order_items oi WHERE oi.product = p.id), 0) " +
                          "FROM products p ORDER BY p.id";
        using var r = cmd.ExecuteReader();
        var list = new List<AuditRow>();
        while (r.Read()) list.Add(new AuditRow(r.GetInt32(0), r.GetString(1), r.GetInt32(2), r.GetInt32(3), r.GetInt32(4)));
        return list;
    }

    /// <summary>Create the tables and, on an empty database, stock the shelves.</summary>
    public void Initialize(string schemaPath)
    {
        using var conn = Open();
        using (var pragma = conn.CreateCommand())
        {
            pragma.CommandText = "PRAGMA journal_mode = WAL;";
            pragma.ExecuteNonQuery();
        }
        using var tx = conn.BeginTransaction();
        using (var cmd = conn.CreateCommand())
        {
            cmd.Transaction = tx;
            cmd.CommandText = File.ReadAllText(schemaPath);
            cmd.ExecuteNonQuery();
        }
        using (var count = conn.CreateCommand())
        {
            count.Transaction = tx;
            count.CommandText = "SELECT COUNT(*) FROM products";
            if (Convert.ToInt32(count.ExecuteScalar()) == 0)
            {
                (string name, string blurb, int price, int stock)[] seed =
                [
                    ("Goldfish", "A classic. Low maintenance, high wobble.", 399, 25),
                    ("Hamster", "Runs all night so you don't have to.", 1499, 8),
                    ("Parakeet", "Chatty, colourful, opinionated.", 2999, 5),
                    ("Tortoise", "Will outlive the codebase.", 8999, 2),
                    ("Kitten", "Verified adorable.", 12000, 3),
                    ("Puppy", "Proof obligations: walks, twice daily.", 25000, 1),
                ];
                // Ids 1 .. N with no gaps: the model's catalog is the range 1 .. nprod.
                for (int i = 0; i < seed.Length; i++)
                {
                    using var ins = conn.CreateCommand();
                    ins.Transaction = tx;
                    ins.CommandText = "INSERT INTO products (id, name, blurb, price_cents, stock, received) " +
                                      "VALUES ($id, $n, $b, $pr, $s, $s)";
                    ins.Parameters.AddWithValue("$id", i + 1);
                    ins.Parameters.AddWithValue("$n", seed[i].name);
                    ins.Parameters.AddWithValue("$b", seed[i].blurb);
                    ins.Parameters.AddWithValue("$pr", seed[i].price);
                    ins.Parameters.AddWithValue("$s", seed[i].stock);
                    ins.ExecuteNonQuery();
                }
            }
        }
        tx.Commit();
    }
}
