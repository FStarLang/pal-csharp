using Microsoft.Data.Sqlite;
using PetStore.Verified;
using PetStore.Web.Data;

var builder = WebApplication.CreateBuilder(args);

var dbPath = builder.Configuration["PetStore:Database"] ?? Path.Combine(builder.Environment.ContentRootPath, "petstore.db");
var connectionString = new SqliteConnectionStringBuilder
{
    DataSource = dbPath,
    Pooling = true,
    DefaultTimeout = 60,   // seconds to wait for another transaction's write lock
}.ToString();

var catalog = new Catalog(connectionString);
catalog.Initialize(Path.Combine(AppContext.BaseDirectory, "Data", "Schema.sql"));

var backend = new SqliteBackend(connectionString);
// One store for the whole process; every request runs its transactions against it.
builder.Services.AddSingleton(catalog);
builder.Services.AddSingleton(backend);
builder.Services.AddSingleton(new Ops(new Store(backend)));
builder.Services.AddRazorPages();

var app = builder.Build();

// A request that throws halfway through a transaction must not keep the write lock.
app.Use(async (http, next) =>
{
    try { await next(http); }
    finally { backend.AbortCurrent(); }
});

if (!app.Environment.IsDevelopment()) app.UseExceptionHandler("/Error");
app.UseStaticFiles();
app.UseRouting();
app.MapRazorPages();

// A small JSON API over the same verified operations, for scripts and the stress test.
var api = app.MapGroup("/api");
api.MapGet("/products", (Catalog cat) => cat.Products());
api.MapGet("/customers/{c:int}/cart", (int c, Catalog cat) =>
    cat.Cart(c).Select(l => new { product = l.Product.Id, l.Product.Name, qty = l.Qty }));
api.MapPost("/customers/{c:int}/cart/{p:int}", (int c, int p, int qty, Ops ops) =>
    { ops.AddToCart(c, p, qty); return Results.NoContent(); });
api.MapPut("/customers/{c:int}/cart/{p:int}", (int c, int p, int qty, Ops ops) =>
    { ops.SetCartQty(c, p, qty); return Results.NoContent(); });
api.MapPost("/customers/{c:int}/checkout", (int c, Ops ops) =>
{
    var r = ops.PlaceOrder(c);
    return Results.Ok(new { accepted = r.OrderId != 0, orderId = r.OrderId });
});
api.MapPost("/products/{p:int}/restock", (int p, int n, Ops ops) =>
    { ops.Restock(p, n); return Results.NoContent(); });
api.MapGet("/orders", (Catalog cat) => cat.Orders(null));
api.MapGet("/audit", (Catalog cat) =>
{
    var rows = cat.Audit();
    return new { ok = rows.All(r => r.Ok), products = rows };
});

app.Run();
