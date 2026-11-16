#!/usr/bin/env python3
"""Concurrent checkout stress test for the verified pet store.

Many customers fill carts and check out at the same time, competing for scarce stock,
while staff restock in parallel. Afterwards we check, against the API:
  * the audit invariant: every pet has stock >= 0 and stock + sold == received;
  * every accepted order contains exactly what that customer had in their cart;
  * every rejected customer's cart is untouched;
  * units sold never exceed units ever received.

Usage: scripts/stress.py [base-url] [customers] [threads]
"""
import json, random, sys, urllib.request
from concurrent.futures import ThreadPoolExecutor

BASE = sys.argv[1] if len(sys.argv) > 1 else "http://127.0.0.1:5077"
CUSTOMERS = int(sys.argv[2]) if len(sys.argv) > 2 else 200
THREADS = int(sys.argv[3]) if len(sys.argv) > 3 else 32

def call(method, path):
    req = urllib.request.Request(BASE + path, method=method)
    with urllib.request.urlopen(req) as r:
        body = r.read()
        return json.loads(body) if body else None

products = call("GET", "/api/products")
ids = [p["id"] for p in products]
base_c = random.randint(1_000_000, 1_000_000_000)

def shopper(i):
    c = base_c + i
    rnd = random.Random(c)
    want = {}
    for p in rnd.sample(ids, rnd.randint(1, 3)):
        q = rnd.randint(1, 3)
        call("POST", f"/api/customers/{c}/cart/{p}?qty={q}")
        want[p] = want.get(p, 0) + q
    r = call("POST", f"/api/customers/{c}/checkout")
    return c, want, r

def restocker(i):
    call("POST", f"/api/products/{random.choice(ids)}/restock?n=1")

with ThreadPoolExecutor(THREADS) as pool:
    shop = [pool.submit(shopper, i) for i in range(CUSTOMERS)]
    stock = [pool.submit(restocker, i) for i in range(CUSTOMERS // 10)]
    results = [f.result() for f in shop]
    for f in stock: f.result()

orders = {o["id"]: o for o in call("GET", "/api/orders")}
accepted = rejected = 0
for c, want, r in results:
    cart = {l["product"]: l["qty"] for l in call("GET", f"/api/customers/{c}/cart")}
    if r["accepted"]:
        accepted += 1
        o = orders[r["orderId"]]
        got = {l["product"]: l["qty"] for l in o["lines"]}
        assert o["customer"] == c, (c, o)
        assert got == want, f"order {o['id']} for {c}: wanted {want}, got {got}"
        assert cart == {}, f"customer {c}'s cart not emptied: {cart}"
    else:
        rejected += 1
        assert r["orderId"] == 0
        assert cart == want, f"rejected customer {c}'s cart changed: {want} -> {cart}"

ids_sorted = sorted(orders)
assert ids_sorted == list(range(1, len(ids_sorted) + 1)), "order ids are not 1..n"

audit = call("GET", "/api/audit")
for row in audit["products"]:
    print(f"  {row['name']:<10} stock {row['stock']:>4}  sold {row['sold']:>4}  received {row['received']:>4}")
assert audit["ok"], "audit failed"
print(f"{CUSTOMERS} concurrent customers: {accepted} orders accepted, {rejected} rejected; "
      f"{len(orders)} orders in total; audit OK")
