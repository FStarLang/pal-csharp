(*
   The pet store's database, as a shared, concurrently accessed resource.

   In the style of FStar's Example.SimpleDBModel: the tables are a reference
   holding a `PetStoreModel.db`, guarded by a lock. Alongside it is a ghost,
   monotonic history: a reference whose successive values may only `evolve`
   by legal business steps. Every transaction holds the lock from `begin_tx`
   to `commit_*`/`rollback`, so clients see each other's transactions as
   atomic, and each commit must justify the change it publishes as one legal
   step from the state it started from.

   Every function below is *implemented and verified* over this model. The C#
   binders (Verified/Db.cs) carry exactly these contracts and are implemented
   with SQL over SQLite instead; that each binder does what its model does,
   and that a SQLite `BEGIN IMMEDIATE` transaction is as exclusive as the
   lock, is the trusted base.
*)
module PetStoreDb
#lang-pulse
open Pulse.Lib.Pervasives
open PetStoreModel

module MR = Pulse.Lib.MonotonicGhostRef
module L = Pulse.Lib.SpinLock
module I32 = FStar.Int32

noeq
type store = {
  db_ref : ref db;
  hist   : MR.mref evolves;
  lock   : L.lock;
}

(* A transaction remembers the state it began in. *)
noeq
type tx = { start : db }

(* What a transaction published: the state it began in, the state it left,
   and the id of the order it accepted (0 if none). *)
noeq
type receipt = { before : db; after : db; order_id : I32.t }

let tx_start (t:tx) : db = t.start
let receipt_before (r:receipt) : db = r.before
let receipt_after (r:receipt) : db = r.after
let receipt_order_id (r:receipt) : int = I32.v r.order_id

(* -------------------------------------------------------------------------
   Ownership predicates.
   ------------------------------------------------------------------------- *)

(* What the lock protects: the tables, the authoritative history, and the
   fact that they agree and satisfy the invariant. *)
let lock_inv_of (r:ref db) (h:MR.mref evolves) : slprop =
  exists* (d:db). pts_to r d ** MR.pts_to h #1.0R d ** pure (inv d)

let lock_inv (s:store) : slprop = lock_inv_of s.db_ref s.hist

(* A client's share of the store. Any number of clients may hold one. *)
let live (s:store) : slprop =
  exists* (f:perm). L.lock_alive s.lock #f (lock_inv s)

(* An open transaction `t` on `s`, which currently sees `cur`. *)
let open_tx ([@@@mkey] s:store) ([@@@mkey] t:tx) (cur:db) : slprop =
  pts_to s.db_ref cur **
  MR.pts_to s.hist #1.0R t.start **
  L.lock_acquired s.lock **
  pure (inv t.start /\ bounded cur /\ cur.nprod == t.start.nprod)

(* Evidence that a receipt's two states were, in that order, states of the
   shared store's history: no other client can make this false. *)
let witnessed (s:store) (r:receipt) : slprop =
  MR.snapshot s.hist r.before **
  MR.snapshot s.hist r.after **
  pure (inv r.before /\ inv r.after /\ evolves r.before r.after)

ghost
fn share_live (s:store)
  requires live s
  ensures live s ** live s
{
  unfold live s;
  L.share s.lock;
  fold live s;
  fold live s;
}

(* -------------------------------------------------------------------------
   Creating the store.
   ------------------------------------------------------------------------- *)

(* A model allocation: the real tables are created by Web/Schema.sql. *)
#push-options "--warn_error -288"
fn create (d:db)
  requires pure (inv d)
  returns s:store
  ensures live s
{
  let r = alloc #db d;
  let h = MR.alloc #db #evolves d;
  fold (lock_inv_of r h);
  let l = L.new_lock (lock_inv_of r h);
  let s = { db_ref = r; hist = h; lock = l };
  rewrite L.lock_alive l #1.0R (lock_inv_of r h) as L.lock_alive s.lock #1.0R (lock_inv s);
  fold live s;
  s
}
#pop-options

(* -------------------------------------------------------------------------
   Transactions.
   ------------------------------------------------------------------------- *)

(* TRUSTED (liveness): acquiring the store's lock returns. Pulse's `L.acquire`
   is `divergent`, since a lock may be held forever; this is the assumption that
   no transaction keeps it, which holds because every operation that opens a
   transaction ends it (each is a terminating `fn` that ends in a commit or a
   rollback). It is the one assumption of this model; everything below is
   verified. *)
assume val acquire (#v:slprop) (#p:perm) (l:L.lock)
  : stt unit (L.lock_alive l #p v) (fun _ -> L.lock_alive l #p v ** v ** L.lock_acquired l)

(* Blocks until no other transaction is open. *)
fn begin_tx (s:store)
  preserves live s
  returns t:tx
  ensures open_tx s t t.start ** pure (inv t.start)
{
  unfold live s;
  acquire s.lock;
  unfold lock_inv s;
  unfold lock_inv_of s.db_ref s.hist;
  with d. assert (pts_to s.db_ref d);
  let v = !s.db_ref;
  inv_bounded v;
  fold live s;
  let t = { start = v };
  rewrite each d as t.start;
  fold (open_tx s t t.start);
  t
}

fn get_nprod (s:store) (t:tx) (#cur:erased db)
  preserves open_tx s t cur
  returns r:I32.t
  ensures pure (I32.v r == nprod_of cur)
{
  unfold open_tx s t cur;
  let d = !s.db_ref;
  fold open_tx s t cur;
  I32.int_to_t d.nprod
}

fn get_stock (s:store) (t:tx) (p:I32.t) (#cur:erased db)
  preserves open_tx s t cur
  returns r:I32.t
  ensures pure (I32.v r == stock_of cur (I32.v p))
{
  unfold open_tx s t cur;
  let d = !s.db_ref;
  fold open_tx s t cur;
  I32.int_to_t (d.stock (I32.v p))
}

fn get_received (s:store) (t:tx) (p:I32.t) (#cur:erased db)
  preserves open_tx s t cur
  returns r:I32.t
  ensures pure (I32.v r == received_of cur (I32.v p))
{
  unfold open_tx s t cur;
  let d = !s.db_ref;
  fold open_tx s t cur;
  I32.int_to_t (d.received (I32.v p))
}

fn get_cart (s:store) (t:tx) (c p:I32.t) (#cur:erased db)
  preserves open_tx s t cur
  returns r:I32.t
  ensures pure (I32.v r == cart_of cur (I32.v c) (I32.v p))
{
  unfold open_tx s t cur;
  let d = !s.db_ref;
  fold open_tx s t cur;
  I32.int_to_t (d.cart (I32.v c) (I32.v p))
}

fn get_next_oid (s:store) (t:tx) (#cur:erased db)
  preserves open_tx s t cur
  returns r:I32.t
  ensures pure (I32.v r == next_oid_of cur)
{
  unfold open_tx s t cur;
  let d = !s.db_ref;
  fold open_tx s t cur;
  I32.int_to_t d.next_oid
}

fn write_stock (s:store) (t:tx) (p v:I32.t) (#cur:erased db)
  requires open_tx s t cur ** pure (0 <= I32.v v)
  ensures open_tx s t (set_stock cur (I32.v p) (I32.v v))
{
  unfold open_tx s t cur;
  let d = !s.db_ref;
  s.db_ref := set_stock d (I32.v p) (I32.v v);
  fold open_tx s t (set_stock cur (I32.v p) (I32.v v));
}

fn write_received (s:store) (t:tx) (p v:I32.t) (#cur:erased db)
  requires open_tx s t cur ** pure (0 <= I32.v v)
  ensures open_tx s t (set_received cur (I32.v p) (I32.v v))
{
  unfold open_tx s t cur;
  let d = !s.db_ref;
  s.db_ref := set_received d (I32.v p) (I32.v v);
  fold open_tx s t (set_received cur (I32.v p) (I32.v v));
}

fn write_cart (s:store) (t:tx) (c p q:I32.t) (#cur:erased db)
  requires open_tx s t cur ** pure (0 <= I32.v q /\ I32.v q <= max_cart_qty)
  ensures open_tx s t (set_cart cur (I32.v c) (I32.v p) (I32.v q))
{
  unfold open_tx s t cur;
  let d = !s.db_ref;
  s.db_ref := set_cart d (I32.v c) (I32.v p) (I32.v q);
  fold open_tx s t (set_cart cur (I32.v c) (I32.v p) (I32.v q));
}

fn write_clear_cart (s:store) (t:tx) (c:I32.t) (#cur:erased db)
  requires open_tx s t cur
  ensures open_tx s t (clear_cart cur (I32.v c))
{
  unfold open_tx s t cur;
  let d = !s.db_ref;
  s.db_ref := clear_cart d (I32.v c);
  fold open_tx s t (clear_cart cur (I32.v c));
}

fn insert_order (s:store) (t:tx) (c:I32.t) (#cur:erased db)
  requires open_tx s t cur ** pure (ids_left cur)
  ensures open_tx s t (add_order cur (I32.v c))
{
  unfold open_tx s t cur;
  let d = !s.db_ref;
  s.db_ref := add_order d (I32.v c);
  fold open_tx s t (add_order cur (I32.v c));
}

(* Publish `cur`, which must be one legal step on from where `t` began. *)
fn commit_step (s:store) (t:tx) (oid:I32.t) (#cur:erased db)
  preserves live s
  requires open_tx s t cur ** pure (evolves t.start cur)
  returns r:receipt
  ensures witnessed s r ** pure (r.before == t.start /\ r.after == reveal cur /\ r.order_id == oid)
{
  unfold open_tx s t cur;
  let d = !s.db_ref;
  evolves_preserves_inv t.start d;
  MR.take_snapshot s.hist t.start;
  MR.update s.hist d;
  MR.take_snapshot s.hist d;
  fold (lock_inv_of s.db_ref s.hist);
  fold (lock_inv s);
  unfold live s;
  L.release s.lock;
  fold live s;
  let r = { before = t.start; after = d; order_id = oid };
  rewrite MR.snapshot s.hist t.start as MR.snapshot s.hist r.before;
  rewrite MR.snapshot s.hist d as MR.snapshot s.hist r.after;
  fold (witnessed s r);
  r
}

fn commit_cart (s:store) (t:tx) (c p q:I32.t) (#cur:erased db)
  preserves live s
  requires open_tx s t cur ** pure (cart_updated t.start cur (I32.v c) (I32.v p) (I32.v q))
  returns r:receipt
  ensures witnessed s r ** pure (r.before == t.start /\ r.after == reveal cur /\ r.order_id == 0l)
{
  cart_update_is_step t.start cur (I32.v c) (I32.v p) (I32.v q);
  commit_step s t 0l
}

fn commit_restock (s:store) (t:tx) (p n:I32.t) (#cur:erased db)
  preserves live s
  requires open_tx s t cur ** pure (restocked t.start cur (I32.v p) (I32.v n))
  returns r:receipt
  ensures witnessed s r ** pure (r.before == t.start /\ r.after == reveal cur /\ r.order_id == 0l)
{
  restock_is_step t.start cur (I32.v p) (I32.v n);
  commit_step s t 0l
}

fn commit_order (s:store) (t:tx) (c oid:I32.t) (#cur:erased db)
  preserves live s
  requires open_tx s t cur ** pure (order_placed t.start cur (I32.v c) (I32.v oid))
  returns r:receipt
  ensures witnessed s r ** pure (r.before == t.start /\ r.after == reveal cur /\ r.order_id == oid)
{
  order_is_step t.start cur (I32.v c) (I32.v oid);
  commit_step s t oid
}

(* Abandon the transaction: the tables go back to how `t` found them. *)
fn rollback (s:store) (t:tx) (#cur:erased db)
  preserves live s
  requires open_tx s t cur
  returns r:receipt
  ensures witnessed s r ** pure (r.before == t.start /\ r.after == t.start /\ r.order_id == 0l)
{
  unfold open_tx s t cur;
  s.db_ref := t.start;
  MR.take_snapshot s.hist t.start;
  MR.take_snapshot s.hist t.start;
  fold (lock_inv_of s.db_ref s.hist);
  fold (lock_inv s);
  unfold live s;
  L.release s.lock;
  fold live s;
  let r = { before = t.start; after = t.start; order_id = 0l };
  rewrite MR.snapshot s.hist t.start as MR.snapshot s.hist r.before;
  rewrite MR.snapshot s.hist t.start as MR.snapshot s.hist r.after;
  fold (witnessed s r);
  r
}
