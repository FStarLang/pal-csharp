-- The pet store's tables. Products are numbered 1 .. N with no gaps: the verified model's
-- catalog is the range 1 .. nprod (PetStoreModel.db).
CREATE TABLE IF NOT EXISTS products (
    id          INTEGER PRIMARY KEY,
    name        TEXT    NOT NULL,
    blurb       TEXT    NOT NULL,
    price_cents INTEGER NOT NULL,
    stock       INTEGER NOT NULL,   -- units on the shelf
    received    INTEGER NOT NULL    -- units ever delivered
);

-- A customer's cart; a missing row means quantity 0.
CREATE TABLE IF NOT EXISTS cart_items (
    customer INTEGER NOT NULL,
    product  INTEGER NOT NULL REFERENCES products(id),
    qty      INTEGER NOT NULL,
    PRIMARY KEY (customer, product)
);

-- Accepted orders. Ids are 1, 2, 3, ... in acceptance order.
CREATE TABLE IF NOT EXISTS orders (
    id        INTEGER PRIMARY KEY,
    customer  INTEGER NOT NULL,
    placed_at TEXT    NOT NULL
);

CREATE TABLE IF NOT EXISTS order_items (
    order_id    INTEGER NOT NULL REFERENCES orders(id),
    product     INTEGER NOT NULL REFERENCES products(id),
    qty         INTEGER NOT NULL,
    price_cents INTEGER NOT NULL,
    PRIMARY KEY (order_id, product)
);
