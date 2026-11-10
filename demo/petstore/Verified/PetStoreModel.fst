(*
   The pet store's database, as a mathematical object.

   This module is the *specification*: what the store's tables hold, which
   transitions of them are legal business operations, and the global invariant
   every reachable state satisfies. It is pure F*; nothing here runs.

   The tables (see Web/Data/Schema.sql):

     products(id, ..., stock, received)               -- `stock`, `received`
     cart_items(customer, product, qty)                 -- `cart`
     orders(id, customer) / order_items(order_id, product, qty)
                                                        -- `orders`, `next_oid`

   Functions stand for tables keyed by integers: a missing row reads as 0.
*)
module PetStoreModel

module R = FStar.ReflexiveTransitiveClosure

let max_i32 : int = 2147483647

(* A customer may hold at most this many units of one product in a cart. *)
let max_cart_qty : int = 99

noeq
type order = {
  oid      : int;
  customer : int;
  items    : int -> int;          (* product -> quantity *)
}

noeq
type db = {
  nprod    : int;                 (* the catalog: products are 1 .. nprod *)
  stock    : int -> int;          (* units on the shelf *)
  received : int -> int;          (* units ever delivered to the store *)
  cart     : int -> int -> int;   (* customer -> product -> quantity *)
  orders   : list order;          (* accepted orders, newest first *)
  next_oid : int;                 (* the id the next accepted order gets *)
}

let is_product (d:db) (p:int) : bool = 1 <= p && p <= d.nprod

(* Observations, named for the C# side. *)
let nprod_of (d:db) : int = d.nprod
let stock_of (d:db) (p:int) : int = d.stock p
let received_of (d:db) (p:int) : int = d.received p
let cart_of (d:db) (c p:int) : int = d.cart c p
let next_oid_of (d:db) : int = d.next_oid

(* -------------------------------------------------------------------------
   Row-level writes: what one SQL statement of a binder does.
   ------------------------------------------------------------------------- *)

let upd (f:int -> int) (k v:int) : int -> int = fun x -> if x = k then v else f x

let set_stock (d:db) (p v:int) : db = { d with stock = upd d.stock p v }

let set_received (d:db) (p v:int) : db = { d with received = upd d.received p v }

let set_cart (d:db) (c p q:int) : db =
  { d with cart = (fun c' -> if c' = c then upd (d.cart c) p q else d.cart c') }

let clear_cart (d:db) (c:int) : db =
  { d with cart = (fun c' -> if c' = c then (fun _ -> 0) else d.cart c') }

(* Insert an order whose lines are the customer's cart, with the next id. *)
let add_order (d:db) (c:int) : db =
  { d with orders = { oid = d.next_oid; customer = c; items = d.cart c } :: d.orders;
           next_oid = d.next_oid + 1 }

(* -------------------------------------------------------------------------
   Business operations: the legal transitions, stated as relations between the
   state before and the state after.
   ------------------------------------------------------------------------- *)

(* A customer's cart can be checked out: it is not empty, and the store has
   every unit it asks for. *)
let cart_nonempty (d:db) (c:int) : prop =
  exists (p:int). {:pattern (d.cart c p)} is_product d p /\ d.cart c p > 0

let in_stock (d:db) (c:int) : prop =
  forall (p:int). {:pattern (d.cart c p) \/ (d.stock p)} is_product d p ==> d.cart c p <= d.stock p

let fillable (d:db) (c:int) : prop = cart_nonempty d c /\ in_stock d c

(* Order ids are Int32s; once they are used up the store accepts no orders. *)
let ids_left (d:db) : prop = d.next_oid < max_i32

(* Customer `c` set the quantity of product `p` in their cart to `q`. *)
let cart_updated (d0 d1:db) (c p q:int) : prop =
  is_product d0 p /\ 0 <= q /\ q <= max_cart_qty /\
  d1.nprod == d0.nprod /\
  (forall (x:int). {:pattern (d1.stock x)} d1.stock x == d0.stock x) /\
  (forall (x:int). {:pattern (d1.received x)} d1.received x == d0.received x) /\
  (forall (c' x:int). {:pattern (d1.cart c' x)} d1.cart c' x == (if c' = c && x = p then q else d0.cart c' x)) /\
  d1.orders == d0.orders /\
  d1.next_oid == d0.next_oid

(* The store received `n` more units of product `p`. *)
let restocked (d0 d1:db) (p n:int) : prop =
  is_product d0 p /\ n > 0 /\ d0.received p + n <= max_i32 /\
  d1.nprod == d0.nprod /\
  (forall (x:int). {:pattern (d1.stock x)} d1.stock x == (if x = p then d0.stock x + n else d0.stock x)) /\
  (forall (x:int). {:pattern (d1.received x)} d1.received x == (if x = p then d0.received x + n else d0.received x)) /\
  (forall (c' x:int). {:pattern (d1.cart c' x)} d1.cart c' x == d0.cart c' x) /\
  d1.orders == d0.orders /\
  d1.next_oid == d0.next_oid

(* Customer `c` checked out, and order `oid` was accepted: the cart was
   fillable; the order holds exactly the cart's lines; those units left the
   shelf; and the cart is now empty. *)
let order_placed (d0 d1:db) (c oid:int) : prop =
  fillable d0 c /\ ids_left d0 /\
  oid == d0.next_oid /\
  d1.nprod == d0.nprod /\
  (forall (x:int). {:pattern (d1.stock x)} d1.stock x ==
     (if is_product d0 x then d0.stock x - d0.cart c x else d0.stock x)) /\
  (forall (x:int). {:pattern (d1.received x)} d1.received x == d0.received x) /\
  (forall (c' x:int). {:pattern (d1.cart c' x)} d1.cart c' x == (if c' = c then 0 else d0.cart c' x)) /\
  Cons? d1.orders /\
  (List.Tot.hd d1.orders).oid == oid /\
  (List.Tot.hd d1.orders).customer == c /\
  (forall (x:int). {:pattern ((List.Tot.hd d1.orders).items x)} (List.Tot.hd d1.orders).items x == d0.cart c x) /\
  List.Tot.tl d1.orders == d0.orders /\
  d1.next_oid == d0.next_oid + 1

(* One legal step, and many. *)
let step : R.binrel db = fun d0 d1 ->
  (exists (c p q:int). cart_updated d0 d1 c p q) \/
  (exists (p n:int). restocked d0 d1 p n) \/
  (exists (c oid:int). order_placed d0 d1 c oid)

let evolves : FStar.Preorder.preorder db = R.closure step

(* Introduction forms, one per operation, so that a client never has to
   choose an existential witness. *)
let cart_update_is_step (d0 d1:db) (c p q:int)
  : Lemma (requires cart_updated d0 d1 c p q) (ensures step d0 d1 /\ evolves d0 d1)
  = R.closure_step step d0 d1

let restock_is_step (d0 d1:db) (p n:int)
  : Lemma (requires restocked d0 d1 p n) (ensures step d0 d1 /\ evolves d0 d1)
  = R.closure_step step d0 d1

let order_is_step (d0 d1:db) (c oid:int)
  : Lemma (requires order_placed d0 d1 c oid) (ensures step d0 d1 /\ evolves d0 d1)
  = R.closure_step step d0 d1

(* -------------------------------------------------------------------------
   The global invariant.
   ------------------------------------------------------------------------- *)

(* Units of product `p` sold, over a list of orders. *)
let rec sold (p:int) (os:list order) : int =
  match os with
  | [] -> 0
  | o :: rest -> o.items p + sold p rest

(* Conservation at product `p`: every unit received is either on the shelf
   or in exactly one accepted order -- so no order was ever accepted without
   stock for it. *)
let conserved_at (d:db) (p:int) : prop =
  0 <= d.stock p /\
  0 <= sold p d.orders /\
  d.stock p + sold p d.orders == d.received p /\
  d.received p <= max_i32

(* Carts hold sensible quantities of catalog products only. *)
let cart_ok_at (d:db) (c p:int) : prop =
  0 <= d.cart c p /\ d.cart c p <= max_cart_qty /\
  (not (is_product d p) ==> d.cart c p == 0)

let inv (d:db) : prop =
  0 <= d.nprod /\ d.nprod < max_i32 /\
  (forall (p:int). {:pattern (conserved_at d p)} conserved_at d p) /\
  (forall (c p:int). {:pattern (cart_ok_at d c p)} cart_ok_at d c p) /\
  (* Order ids are 1, 2, 3, ... in acceptance order. *)
  d.next_oid == List.Tot.length d.orders + 1 /\
  d.next_oid <= max_i32

(* A fresh store: the catalog, with what was delivered on day one. *)
let initial (n:int) (delivered:int -> int) : db = {
  nprod = n;
  stock = delivered;
  received = delivered;
  cart = (fun _ _ -> 0);
  orders = [];
  next_oid = 1;
}

let initial_inv (n:int) (delivered:int -> int)
  : Lemma (requires 0 <= n /\ n < max_i32 /\
                    (forall (p:int). 0 <= delivered p /\ delivered p <= max_i32))
          (ensures inv (initial n delivered))
  = ()

let inv_intro (d:db)
  : Lemma (requires 0 <= d.nprod /\ d.nprod < max_i32 /\
                    (forall (p:int). conserved_at d p) /\
                    (forall (c p:int). cart_ok_at d c p) /\
                    d.next_oid == List.Tot.length d.orders + 1 /\
                    d.next_oid <= max_i32)
          (ensures inv d)
  = ()

let sold_cons (p:int) (o:order) (rest:list order)
  : Lemma (sold p (o :: rest) == o.items p + sold p rest)
  = ()

let length_cons (o:order) (rest:list order)
  : Lemma (List.Tot.length (o :: rest) == List.Tot.length rest + 1)
  = ()

#push-options "--fuel 0 --ifuel 1"
let cart_update_preserves_inv (d0 d1:db) (c p q:int)
  : Lemma (requires inv d0 /\ cart_updated d0 d1 c p q) (ensures inv d1)
  = introduce forall (x:int). conserved_at d1 x
    with assert (conserved_at d0 x);
    introduce forall (c' x:int). cart_ok_at d1 c' x
    with (assert (cart_ok_at d0 c' x);
          assert (d1.cart c' x == (if c' = c && x = p then q else d0.cart c' x));
          assert (is_product d1 x == is_product d0 x));
    inv_intro d1

let restock_preserves_inv (d0 d1:db) (p n:int)
  : Lemma (requires inv d0 /\ restocked d0 d1 p n) (ensures inv d1)
  = introduce forall (x:int). conserved_at d1 x
    with assert (conserved_at d0 x);
    introduce forall (c' x:int). cart_ok_at d1 c' x
    with assert (cart_ok_at d0 c' x);
    inv_intro d1

let order_preserves_inv (d0 d1:db) (c oid:int)
  : Lemma (requires inv d0 /\ order_placed d0 d1 c oid) (ensures inv d1)
  = let o = List.Tot.hd d1.orders in
    let rest = List.Tot.tl d1.orders in
    assert (d1.orders == o :: rest);
    introduce forall (x:int). conserved_at d1 x
    with (sold_cons x o rest;
          assert (conserved_at d0 x);
          assert (cart_ok_at d0 c x));
    introduce forall (c' x:int). cart_ok_at d1 c' x
    with assert (cart_ok_at d0 c' x);
    length_cons o rest;
    inv_intro d1
#pop-options

let step_preserves_inv (d0 d1:db)
  : Lemma (requires inv d0 /\ step d0 d1) (ensures inv d1)
  = eliminate (exists (c p q:int). cart_updated d0 d1 c p q) \/
              ((exists (p n:int). restocked d0 d1 p n) \/
               (exists (c oid:int). order_placed d0 d1 c oid))
    with (eliminate exists (c p q:int). cart_updated d0 d1 c p q
          with cart_update_preserves_inv d0 d1 c p q)
    and (eliminate (exists (p n:int). restocked d0 d1 p n) \/
                   (exists (c oid:int). order_placed d0 d1 c oid)
         with (eliminate exists (p n:int). restocked d0 d1 p n
               with restock_preserves_inv d0 d1 p n)
         and (eliminate exists (c oid:int). order_placed d0 d1 c oid
              with order_preserves_inv d0 d1 c oid))

(* THE TOP-LEVEL THEOREM, part 1.

   Whatever interleaving of operations by however many concurrent clients took
   the database from a state satisfying the invariant (e.g. `initial`) to `d1`,
   `d1` satisfies it too. In particular, for every product, the units sold
   across all accepted orders never exceed the units ever received. *)
let evolves_preserves_inv (d0 d1:db)
  : Lemma (requires inv d0 /\ evolves d0 d1) (ensures inv d1)
  = Classical.forall_intro_2 (fun x y -> Classical.move_requires (step_preserves_inv x) y);
    R.stable_on_closure step inv ()

let no_oversell (d0 d1:db) (p:int)
  : Lemma (requires inv d0 /\ evolves d0 d1)
          (ensures 0 <= d1.stock p /\ sold p d1.orders <= d1.received p)
  = evolves_preserves_inv d0 d1;
    assert (conserved_at d1 p)

(* What the C# code may rely on at the start of a transaction: everything in a
   state satisfying the invariant fits in an Int32. *)
let bounded (d:db) : prop =
  (forall (p:int). {:pattern (d.stock p)} 0 <= d.stock p /\ d.stock p <= max_i32) /\
  (forall (p:int). {:pattern (d.received p)} 0 <= d.received p /\ d.received p <= max_i32) /\
  (forall (c p:int). {:pattern (d.cart c p)} 0 <= d.cart c p /\ d.cart c p <= max_cart_qty) /\
  0 < d.next_oid /\ d.next_oid <= max_i32 /\
  0 <= d.nprod /\ d.nprod < max_i32

let bounded_intro (d:db)
  : Lemma (requires
             (forall (p:int). 0 <= d.stock p /\ d.stock p <= max_i32) /\
             (forall (p:int). 0 <= d.received p /\ d.received p <= max_i32) /\
             (forall (c p:int). 0 <= d.cart c p /\ d.cart c p <= max_cart_qty) /\
             0 < d.next_oid /\ d.next_oid <= max_i32 /\
             0 <= d.nprod /\ d.nprod < max_i32)
          (ensures bounded d)
  = ()

let inv_bounded (d:db) : Lemma (requires inv d) (ensures bounded d)
  = introduce forall (p:int). 0 <= d.stock p /\ d.stock p <= max_i32
    with assert (conserved_at d p);
    introduce forall (p:int). 0 <= d.received p /\ d.received p <= max_i32
    with assert (conserved_at d p);
    introduce forall (c p:int). 0 <= d.cart c p /\ d.cart c p <= max_cart_qty
    with assert (cart_ok_at d c p);
    bounded_intro d

(* -------------------------------------------------------------------------
   What the C# code computes, one product at a time.

   The verified C# walks the catalog 1 .. nprod. These functions are the
   states of those walks after products 1 .. k-1, so a loop invariant can
   name them without an existential.
   ------------------------------------------------------------------------- *)

let rank (k:int) : nat = if k < 1 then 0 else k

(* Some product before `k` is in customer `c`'s cart. *)
let rec any_upto (d:db) (c k:int) : Tot bool (decreases (rank k)) =
  if k <= 1 then false else any_upto d c (k - 1) || d.cart c (k - 1) > 0

(* Every product before `k` has enough stock for customer `c`'s cart. *)
let rec stocked_upto (d:db) (c k:int) : Tot bool (decreases (rank k)) =
  if k <= 1 then true else stocked_upto d c (k - 1) && d.cart c (k - 1) <= d.stock (k - 1)

(* The shelf after the units in `c`'s cart of products before `k` are taken. *)
let rec take_upto (d:db) (c k:int) : Tot db (decreases (rank k)) =
  if k <= 1 then d
  else let d' = take_upto d c (k - 1) in
       if d.cart c (k - 1) > 0 then set_stock d' (k - 1) (d.stock (k - 1) - d.cart c (k - 1)) else d'

let rec any_upto_iff (d:db) (c k:int)
  : Lemma (ensures any_upto d c k <==> (exists (p:int). {:pattern (d.cart c p)} 1 <= p /\ p < k /\ d.cart c p > 0))
          (decreases (rank k))
  = if k <= 1 then () else any_upto_iff d c (k - 1)

let rec stocked_upto_iff (d:db) (c k:int)
  : Lemma (ensures stocked_upto d c k <==>
                   (forall (p:int). {:pattern (d.cart c p)} 1 <= p /\ p < k ==> d.cart c p <= d.stock p))
          (decreases (rank k))
  = if k <= 1 then () else stocked_upto_iff d c (k - 1)

let rec take_upto_frame (d:db) (c k:int)
  : Lemma (ensures (let d' = take_upto d c k in
                    d'.nprod == d.nprod /\ d'.received == d.received /\ d'.cart == d.cart /\
                    d'.orders == d.orders /\ d'.next_oid == d.next_oid /\
                    (forall (x:int). {:pattern (d'.stock x)}
                       d'.stock x == (if 1 <= x && x < k && d.cart c x > 0
                                      then d.stock x - d.cart c x else d.stock x))))
          (decreases (rank k))
          [SMTPat (take_upto d c k)]
  = if k <= 1 then () else take_upto_frame d c (k - 1)

(* The scan the C# checkout performs decides `fillable`. *)
let fillable_iff (d:db) (c:int)
  : Lemma (requires inv d)
          (ensures fillable d c <==> (any_upto d c (d.nprod + 1) && stocked_upto d c (d.nprod + 1)))
  = any_upto_iff d c (d.nprod + 1);
    stocked_upto_iff d c (d.nprod + 1);
    introduce forall (p:int). not (is_product d p) ==> d.cart c p == 0
    with assert (cart_ok_at d c p);
    introduce forall (p:int). 0 <= d.cart c p
    with assert (cart_ok_at d c p)

(* The state a successful checkout leaves behind. *)
let checkout (d:db) (c:int) : db = clear_cart (add_order (take_upto d c (d.nprod + 1)) c) c

let checkout_placed (d:db) (c:int)
  : Lemma (requires inv d /\ fillable d c /\ ids_left d)
          (ensures order_placed d (checkout d c) c d.next_oid)
  = let d1 = checkout d c in
    let t = take_upto d c (d.nprod + 1) in
    take_upto_frame d c (d.nprod + 1);
    introduce forall (x:int). 0 <= d.cart c x /\ (not (is_product d x) ==> d.cart c x == 0)
    with assert (cart_ok_at d c x);
    assert (d1.stock == t.stock /\ d1.received == d.received /\ d1.nprod == d.nprod)

(* The state a restock leaves behind. *)
let restock_result (d:db) (p n:int) : db =
  set_received (set_stock d p (d.stock p + n)) p (d.received p + n)

let restock_ok (d:db) (p n:int)
  : Lemma (requires is_product d p /\ n > 0 /\ d.received p + n <= max_i32)
          (ensures restocked d (restock_result d p n) p n)
  = ()

let cart_update_ok (d:db) (c p q:int)
  : Lemma (requires is_product d p /\ 0 <= q /\ q <= max_cart_qty)
          (ensures cart_updated d (set_cart d c p q) c p q)
  = ()

let stock_le_received (d:db) (p:int)
  : Lemma (requires inv d) (ensures 0 <= d.stock p /\ d.stock p <= d.received p)
  = assert (conserved_at d p)

let stocked_at (d:db) (c k p:int)
  : Lemma (requires stocked_upto d c k /\ 1 <= p /\ p < k) (ensures d.cart c p <= d.stock p)
  = stocked_upto_iff d c k

let cart_bounded (d:db) (c p:int)
  : Lemma (requires inv d) (ensures 0 <= d.cart c p /\ d.cart c p <= max_cart_qty)
  = assert (cart_ok_at d c p)
