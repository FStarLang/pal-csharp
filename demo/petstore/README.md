# Verified Pet Store

An ASP.NET Core (Razor Pages) pet store backed by SQLite. It has a catalog, a shopping
cart and a dummy checkout. Its business logic is written in ordinary C# and verified with
pal-csharp against a model of the database that is shared by many concurrent clients.

```
demo/petstore/
  Verified/                 the verified core (translated by palcs, checked by F*/Pulse)
    PetStoreModel.fst       the specification: tables, legal operations, invariant, theorems
    PetStoreDb.fst          the concurrent database model (Pulse): lock + ghost history
    Db.cs                   C# faces of the model, and the SQL binders ([Implements])
    Ops.cs                  the business operations: Restock, SetCartQty, AddToCart, PlaceOrder
    StoreBackend.cs         the abstract runtime interface the binders call
  Web/                      the web app (unverified UI, plus the SQLite backend)
    Data/Schema.sql         the tables
    Data/SqliteBackend.cs   one SQL statement per binder
    Data/Catalog.cs         read-only display queries and the audit
    Pages/                  Shop, Cart, Orders, Staff (restock + live audit)
  scripts/stress.py         concurrent checkout stress test
```

## The top-level statement of correctness

The state of the whole database is a value `d : PetStoreModel.db`. It has the catalog
`1..nprod`, `stock p`, `received p` (units ever delivered), `cart c p`, the list of
accepted `orders`, and `next_oid`. The legal transitions are three relations:
`cart_updated`, `restocked` and `order_placed`. `evolves` is their reflexive-transitive
closure.

### 1. Every client operation is exactly a legal transition, atomically

`Ops.PlaceOrder(c)`, verified in `Ops.cs`, has this contract:

```csharp
[Requires("Db.Live(s)")]
[Ensures("Db.Live(s)")]
[Ensures("Db.Witnessed(s, Result)")]
[Ensures("Pal.Implies(Model.Fillable(Result.Before, c) && Model.IdsLeft(Result.Before), " +
         "Result.OrderId == Result.Before.NextOid && " +
         "Model.OrderPlaced(Result.Before, Result.After, c, Result.OrderId))")]
[Ensures("Pal.Implies(!(Model.Fillable(Result.Before, c) && Model.IdsLeft(Result.Before)), " +
         "Result.OrderId == 0 && Pal.Same(Result.After, Result.Before))")]
public Receipt PlaceOrder(int c)
```

`Witnessed(s, r)` is the key to concurrency. It holds ghost *snapshots* of the store's
monotonic history at `r.Before` and at `r.After`. So `Before` is the state of the shared
database at the instant the transaction took the lock, and `After` is the state it
published when it released it. No other client's write lies between them, whatever the
interleaving. The contract therefore says:

* **Accepted only when there is inventory.** An order is accepted (`OrderId != 0`) only
  when the cart, read atomically, is non-empty and `cart c p <= stock p` for every
  product (`fillable`).
* **Placed exactly as requested.** When it is accepted, the new state is precisely
  `order_placed`:
  * the order's lines are exactly the customer's cart;
  * each product's stock drops by exactly the quantity ordered;
  * the cart is emptied;
  * the order gets the next id;
  * nothing else changes.
* **Rejected means nothing happened.** An order is rejected only when the cart is empty
  or something is short, or the Int32 order ids have run out. A rejection leaves the
  database unchanged. Nothing is reserved, and no stock is half-taken.

`Restock`, `SetCartQty` and `AddToCart` have the same form, with `restocked` and
`cart_updated`. Every operation leaves `Live(s)` behind, so any number of request threads
may run them concurrently.

### 2. The invariant holds in every reachable state, under any interleaving

In `PetStoreModel.fst`:

```fstar
let conserved_at (d:db) (p:int) : prop =
  0 <= d.stock p /\ 0 <= sold p d.orders /\
  d.stock p + sold p d.orders == d.received p /\ d.received p <= max_i32

val evolves_preserves_inv (d0 d1:db)
  : Lemma (requires inv d0 /\ evolves d0 d1) (ensures inv d1)

val no_oversell (d0 d1:db) (p:int)
  : Lemma (requires inv d0 /\ evolves d0 d1)
          (ensures 0 <= d1.stock p /\ sold p d1.orders <= d1.received p)
```

The lock invariant in `PetStoreDb.fst` keeps `inv` true of the database whenever nobody
holds the lock. The history can only advance by `evolves`, because the ghost history is
an `MR.mref evolves`. As a result, every state any client ever observes satisfies `inv`.
Every unit ever delivered is either still on the shelf or in exactly one accepted order.
Stock is never negative. No product was ever sold more times than it was received.

## Verify it

From the repository root, build the tools once (see the top-level README), then:

```sh
cd demo/petstore/Verified
make -j          # `cs`: builds the C# with the stock compiler; `verify`: palcs + F*/Pulse
```

`make` translates `Db.cs` and `Ops.cs` with `palcs` and checks the result in F*/Pulse,
along with `PetStoreModel.fst` and `PetStoreDb.fst`. It finishes with `0 error(s)` and no
`admit` anywhere in `out/`. It reports one PALCS0904 warning per SQL binder: the binder's
contract is proved against the model, and its SQL is trusted to behave like the model
(see below).

## Run it

```sh
cd demo/petstore/Web
dotnet run --urls http://localhost:5077        # database: ./petstore.db (created and seeded)
```

Open <http://localhost:5077>. Shop, fill a cart, and check out. The **Staff** page
restocks, and audits the invariant against the live tables
(`stock >= 0 && stock + sold == received` for every pet).

There is also a JSON API over the same operations:

| Method | Path | Operation |
|---|---|---|
| `GET`  | `/api/products` | catalog with stock |
| `POST` | `/api/customers/{c}/cart/{p}?qty=n` | `Ops.AddToCart` |
| `PUT`  | `/api/customers/{c}/cart/{p}?qty=n` | `Ops.SetCartQty` |
| `POST` | `/api/customers/{c}/checkout` | `Ops.PlaceOrder` → `{accepted, orderId}` |
| `POST` | `/api/products/{p}/restock?n=k` | `Ops.Restock` |
| `GET`  | `/api/orders`, `/api/audit` | display / audit |

The stress test runs hundreds of customers against scarce stock, in parallel with
restocks. It then checks the audit, that every accepted order equals the customer's cart,
that every rejected cart is untouched, and that order ids run 1..n:

```sh
python3 scripts/stress.py http://localhost:5077 300 48
```

## What is trusted

The proof covers `Ops.cs`, which is translated from the C# that actually runs. It rests
on the following assumptions:

1. **The SQL in the binders** (`Sql` in `Db.cs`) and `SqliteBackend`. Each binder carries
   `[Implements("PetStoreDb.<fn> …")]`, so palcs translates it as a call to the
   verified model function, and F* *checks* that the function's contract implies the
   binder's C# `[Requires]`/`[Ensures]`. If they drift apart, verification fails; this
   caught a real mismatch (`Begin` promised `Inv(Result.Start)` before the model's
   `begin_tx` did). What is left trusted is that the SQL statement does to the tables
   what the model function does to the model (for example, `write_stock` updates
   `stock p` and nothing else).
2. **The SpecType bindings.** `Store`, `Tx` and `Receipt` stand for `PetStoreDb.store`,
   `tx` and `receipt`. The runtime `Receipt.OrderId` getter is trusted to return the
   order id the receipt was created with.
3. **SQLite's isolation.** `BEGIN IMMEDIATE` takes the database's write lock, and every
   operation's reads and writes happen inside that transaction. This is trusted to
   serialize transactions the way `L.acquire`/`L.release` on the model's lock does.
4. **Liveness is not proved.** Acquiring a lock may block. The model makes this a single
   explicit assumption, `assume val acquire` in `PetStoreDb.fst`: it returns the lock's
   invariant, as `L.acquire` does, but is stated as terminating. So the theorem is one
   of partial correctness: if an operation returns, its contract holds.
5. **Everything else in `Web/`.** That covers the UI, the cookie that names the customer,
   and the read-only display queries. None of it writes to the database except through
   `Ops`.
