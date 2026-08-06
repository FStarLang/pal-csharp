module SegmentFacts
#lang-pulse

/// §0 probe for §12: *user-defined ownership predicates*.
///
/// §10 derives a class's ownership predicate from its `[Model]`: one downward fold over
/// one recursive field. That is enough for a singly linked list and a tree, and R10.10
/// stretches it to a whole doubly linked list by carrying the predecessor as an extra
/// index. It is not enough in general, and a *list segment* is the smallest honest
/// counterexample:
///
///   * a segment is bounded at *both* ends, so it has two more pointer parameters than
///     any fold over the class's fields could produce;
///   * its nil case is not `x == None` but `from == to_`, which is a relation between two
///     parameters rather than a property of one;
///   * the interesting lemma -- that two adjacent segments compose -- is a statement about
///     two instances of the predicate at once, and no amount of reading a `[Model]`
///     backwards will produce it.
///
/// So §12's answer is not another knob. It is the same answer §11 gave one level down:
/// the user writes the predicate, and the compiler is told about it rather than taught it.
/// This file is what a user would write, and it pins every fact §12's rules depend on.
///
/// The representation below is *exactly* what the emitter already produces for a class
/// (see `test/linked_list/out/Class_Node.fst`): a record of fields, a box of it, and an
/// option of that. That is the whole of what §12 asks the compiler for -- R12.1's `[Plain]`
/// class is this and nothing else, with no `__inv_opt`, no derived lemmas and no automatic
/// ownership anywhere.

open Pulse
module B = Pulse.Lib.Box
module I32 = FStar.Int32
module L = FStar.List.Tot

// ===========================================================================
// 1. The representation: R12.1's `[Plain]` class, and all of it
// ===========================================================================

///   [Plain]
///   public sealed class DNode
///   {
///       internal int value;
///       internal DNode? prev;
///       internal DNode? next;
///   }
noeq type class_DNode__raw = {
  fld_value: I32.t;
  fld_prev: class_DNode__opt;
  fld_next: class_DNode__opt;
}
and class_DNode = B.box class_DNode__raw
and class_DNode__opt = option class_DNode

// ===========================================================================
// 2. The user's predicate: a doubly linked list *segment*
// ===========================================================================

/// `dll_seg p from prev to_ last l` owns the nodes `from`, ..., `last` -- and nothing
/// else -- holding the values `l`, where
///
///   * `from` is the first node of the segment, or `to_` if it is empty;
///   * `prev` is what the first node's `prev` field must equal (the segment's left
///     boundary; `None` for a whole list);
///   * `to_` is one *past* the last node -- the segment does not own it;
///   * `last` is the final node of the segment, whose `next` is `to_`, or `prev` if the
///     segment is empty.
///
/// The four boundary parameters are the point. `to_` and `last` are what make this a
/// segment rather than a list, and neither can be read off the class: they are chosen by
/// whoever states the specification. `prev` and `last` are what make it *doubly* linked:
/// every back pointer is constrained by a `pure` equation rather than owned, because the
/// cell it points at is already owned by the node before it. Owning it twice is exactly
/// the unsoundness the equations avoid.
let rec dll_seg (p: perm) ([@@@mkey] from: class_DNode__opt)
                (prev: class_DNode__opt) (to_: class_DNode__opt)
                (last: class_DNode__opt) (l: list int)
  : Tot slprop (decreases l)
  = match l with
    | [] -> pure (from == to_ /\ prev == last)
    | hd :: tl ->
      exists* (v: class_DNode) (r: class_DNode__raw).
        pure (from == Some v) **
        B.pts_to v #p r **
        pure (hd == I32.v r.fld_value /\ r.fld_prev == prev) **
        dll_seg p r.fld_next from to_ last tl

/// A whole list is the segment that runs off both ends: nothing before the head, nothing
/// after the tail. This is the shape a `[Refine]` handle class would carry (R12.3).
let is_dll (p: perm) (head: class_DNode__opt) (tail: class_DNode__opt) (l: list int)
  : slprop
  = dll_seg p head None None tail l

// ===========================================================================
// 3. The lemmas the user writes: open and close, at each end
// ===========================================================================

ghost fn dll_seg_intro_nil (p: perm) (from: class_DNode__opt) (prev: class_DNode__opt)
  requires emp
  ensures dll_seg p from prev from prev []
{
  fold (dll_seg p from prev from prev []);
}

ghost fn dll_seg_elim_nil (p: perm) (from: class_DNode__opt) (prev to_ last: class_DNode__opt)
    (#l: list int)
  requires dll_seg p from prev to_ last l ** pure (l == [])
  ensures pure (from == to_ /\ prev == last)
{
  rewrite (dll_seg p from prev to_ last l) as (dll_seg p from prev to_ last []);
  unfold (dll_seg p from prev to_ last []);
}

/// Opening a non-empty segment at the *left*. This is the step a forward traversal takes,
/// and the `r.fld_prev == prev` it hands back is what a backward step later consumes.
/// A non-empty segment starts at a real node. This has to be its own step, because the
/// `Some?` refinement on `elim_cons`'s binder is what lets the elimination name the node as
/// `Some?.v from` -- a *program* pointer -- rather than as an existential the caller could
/// only use in ghost position.
ghost fn dll_seg_some (p: perm) (from: class_DNode__opt) (prev to_ last: class_DNode__opt)
    (#l: list int)
  preserves dll_seg p from prev to_ last l
  requires pure (Cons? l)
  ensures pure (Some? from)
{
  match l {
    [] -> {
      unfold (dll_seg p from prev to_ last []);
      fold (dll_seg p from prev to_ last []);
    }
    hd :: tl -> {
      unfold (dll_seg p from prev to_ last (hd :: tl));
      with v r. assert (B.pts_to v #p r);
      fold (dll_seg p from prev to_ last (hd :: tl));
    }
  }
}

ghost fn dll_seg_elim_cons (p: perm) (from: class_DNode__opt { Some? from })
    (prev to_ last: class_DNode__opt) (#l: list int)
  requires dll_seg p from prev to_ last l ** pure (Cons? l)
  ensures exists* (r: class_DNode__raw) (tl: list int).
    B.pts_to (Some?.v from) #p r **
    dll_seg p r.fld_next from to_ last tl **
    pure (l == I32.v r.fld_value :: tl /\ r.fld_prev == prev)
{
  match l {
    [] -> {
      unfold (dll_seg p from prev to_ last []);
      unreachable ()
    }
    hd :: tl -> {
      unfold (dll_seg p from prev to_ last (hd :: tl));
      with v r. assert (B.pts_to v #p r);
      rewrite each v as (Some?.v from);
    }
  }
}

/// Closing a segment at the left. The node's own `prev` field supplies the new left
/// boundary, so a write to `prev` needs no separate obligation -- re-closing simply
/// reports the boundary the field now holds. That is the same trick R10.10 uses, and it
/// is what makes `push_front` below an ordinary field write.
ghost fn dll_seg_intro_cons (p: perm) (v: class_DNode) (to_ last: class_DNode__opt)
    (#r: class_DNode__raw) (#tl: list int)
  requires B.pts_to v #p r ** dll_seg p r.fld_next (Some v) to_ last tl
  ensures dll_seg p (Some v) r.fld_prev to_ last (I32.v r.fld_value :: tl)
{
  fold (dll_seg p (Some v) r.fld_prev to_ last (I32.v r.fld_value :: tl));
}

// ===========================================================================
// 4. The lemma that no `[Model]` could produce: segments compose
// ===========================================================================

/// Two adjacent segments make one. This is a statement about *two* instances of the
/// predicate, relating four boundary pointers, and it is the whole reason segments exist:
/// it is what lets a loop walk a prefix and put it back.
///
/// It is proved by induction on the first segment's model, which is why it is a `ghost fn
/// rec` rather than anything the emitter could place.
ghost fn rec dll_seg_append (p: perm) (a: class_DNode__opt) (pa: class_DNode__opt)
    (b: class_DNode__opt) (lb: class_DNode__opt)
    (c: class_DNode__opt) (lc: class_DNode__opt)
    (#l1 #l2: list int)
  requires dll_seg p a pa b lb l1 ** dll_seg p b lb c lc l2
  ensures dll_seg p a pa c lc (L.append l1 l2)
  decreases l1
{
  match l1 {
    [] -> {
      dll_seg_elim_nil p a pa b lb #l1;
      rewrite (dll_seg p b lb c lc l2) as (dll_seg p a pa c lc (L.append l1 l2));
    }
    hd :: tl -> {
      dll_seg_some p a pa b lb #l1;
      dll_seg_elim_cons p a pa b lb #l1;
      with r tl'. assert (dll_seg p r.fld_next a b lb tl');
      dll_seg_append p r.fld_next a b lb c lc #tl' #l2;
      dll_seg_intro_cons p (Some?.v a) c lc #r #(L.append tl' l2);
      rewrite (dll_seg p (Some (Some?.v a)) r.fld_prev c lc
                 (I32.v r.fld_value :: L.append tl' l2))
           as (dll_seg p a pa c lc (L.append l1 l2));
    }
  }
}

/// Extending a segment on the *right* by one node -- the step an iterative traversal takes
/// when it advances its cursor. It is `dll_seg_append` against a one-element segment, and
/// it is what §10.7's refused iterative traversal was missing.
ghost fn dll_seg_snoc (p: perm) (a: class_DNode__opt) (pa: class_DNode__opt)
    (v: class_DNode) (c: class_DNode__opt)
    (#l1: list int) (#r: class_DNode__raw)
  requires dll_seg p a pa (Some v) c l1 ** B.pts_to v #p r **
           pure (r.fld_prev == c)
  ensures dll_seg p a pa r.fld_next (Some v) (L.append l1 [I32.v r.fld_value])
{
  dll_seg_intro_nil p r.fld_next (Some v);
  dll_seg_intro_cons p v r.fld_next (Some v) #r #[];
  rewrite (dll_seg p (Some v) r.fld_prev r.fld_next (Some v) (I32.v r.fld_value :: []))
       as (dll_seg p (Some v) c r.fld_next (Some v) [I32.v r.fld_value]);
  dll_seg_append p a pa (Some v) c r.fld_next (Some v) #l1 #[I32.v r.fld_value];
}

// ===========================================================================
// 5. Programs over the user's predicate
// ===========================================================================

/// This is §10's `__cases`, and the restriction on it is the point.
///
/// `Some? from <==> Cons? l` holds only when the right boundary is `None` -- that is, only
/// for a *whole list*. For a general segment the empty case is `from == to_`, which is a
/// relation between two parameters, so emptiness is decided by comparing the cursor with
/// the boundary and not by comparing it with null. A C# `if (x == null)` therefore means
/// something weaker than §10 assumes as soon as segments are in play, which is exactly why
/// §12 refuses to *derive* this lemma and makes the user state and prove it.
ghost fn dll_cases (p: perm) (from: class_DNode__opt) (prev: class_DNode__opt)
    (last: class_DNode__opt) (#l: list int)
  preserves dll_seg p from prev None last l
  ensures pure (Some? from <==> Cons? l)
{
  match l {
    [] -> {
      unfold (dll_seg p from prev None last []);
      fold (dll_seg p from prev None last []);
    }
    hd :: tl -> {
      unfold (dll_seg p from prev None last (hd :: tl));
      with v r. assert (B.pts_to v #p r);
      fold (dll_seg p from prev None last (hd :: tl));
    }
  }
}

/// A forward traversal. The body is the ordinary §10 shape -- a null test, a `__cases`
/// before it, an elim in one arm and an intro at the end -- but *every* proof step here is
/// a call to a lemma the user wrote, and §12's job is only to place calls the user named.
fn rec seg_length (p: perm) (from: class_DNode__opt) (prev: class_DNode__opt)
    (#l: erased (list int))
  requires dll_seg p from prev None None l ** pure (L.length l < 2147483647)
  returns  n: I32.t
  ensures  dll_seg p from prev None None l ** pure (I32.v n == L.length l)
  decreases (reveal l)
{
  dll_cases p from prev None #l;
  if (None? from) {
    0l
  } else {
    dll_seg_elim_cons p from prev None None #l;
    with r tl. assert (dll_seg p r.fld_next from None None tl);
    // A ghost binder cannot feed a stateful call, so the node is *read* -- which is what
    // the emitter does anyway (R3.8), and the `pts_to` says the value read is `r`.
    let node = B.op_Bang (Some?.v from);
    let rest = seg_length p node.fld_next from #tl;
    dll_seg_intro_cons p (Some?.v from) None None #r #tl;
    rewrite (dll_seg p (Some (Some?.v from)) r.fld_prev None None (I32.v r.fld_value :: tl))
         as (dll_seg p from prev None None l);
    I32.add rest 1l
  }
}

/// Pushing a new node onto the front, which *writes the old head's back pointer*. This is
/// the operation a singly linked list cannot express at all. Here it is an ordinary field
/// write bracketed by two of the user's lemmas -- and closing the segment reports the
/// boundary the field now holds, which is why the write needs no separate obligation.
fn dll_push_front (head: class_DNode__opt) (tail: class_DNode__opt) (v: I32.t)
    (#l: erased (list int))
  requires is_dll 1.0R head tail l
  returns  h: class_DNode
  ensures  exists* t. is_dll 1.0R (Some h) t (I32.v v :: l)
{
  let n = B.alloc ({ fld_value = v; fld_prev = None; fld_next = head });
  unfold (is_dll 1.0R head tail l);
  dll_cases 1.0R head None tail #l;

  if (Some? head) {
    dll_seg_elim_cons 1.0R head None None tail #l;
    with hr htl. assert (dll_seg 1.0R hr.fld_next head None tail htl);
    let hnode = B.op_Bang (Some?.v head);
    B.op_Colon_Equals (Some?.v head) ({ hnode with fld_prev = Some n });
    rewrite (dll_seg 1.0R hr.fld_next head None tail htl)
         as (dll_seg 1.0R ({ hnode with fld_prev = Some n }).fld_next
                          (Some (Some?.v head)) None tail htl);
    dll_seg_intro_cons 1.0R (Some?.v head) None tail #({ hnode with fld_prev = Some n }) #htl;
    rewrite (dll_seg 1.0R (Some (Some?.v head)) (Some n) None tail
               (I32.v ({ hnode with fld_prev = Some n }).fld_value :: htl))
         as (dll_seg 1.0R ({ fld_value = v; fld_prev = None; fld_next = head }).fld_next
                          (Some n) None tail l);
    dll_seg_intro_cons 1.0R n None tail
      #({ fld_value = v; fld_prev = None; fld_next = head }) #l;
    fold (is_dll 1.0R (Some n) tail (I32.v v :: l));
    n
  } else {
    dll_seg_elim_nil 1.0R head None None tail #l;
    dll_seg_intro_nil 1.0R head (Some n);
    rewrite (dll_seg 1.0R head (Some n) head (Some n) [])
         as (dll_seg 1.0R ({ fld_value = v; fld_prev = None; fld_next = head }).fld_next
                          (Some n) None (Some n) l);
    dll_seg_intro_cons 1.0R n None (Some n)
      #({ fld_value = v; fld_prev = None; fld_next = head }) #l;
    fold (is_dll 1.0R (Some n) (Some n) (I32.v v :: l));
    n
  }
}

// ===========================================================================
// 6. The style §12 asks for: one publishable lemma per C# step
// ===========================================================================

/// §5 above is faithful Pulse, and it is unusable as a *target*. Every program there
/// carries `with r tl. assert (...)` to name an existential the predicate hid, and a
/// `rewrite ... as ...` to move between the nullable cursor `from` and the boxed node
/// `Some?.v from` the emitter reads through. Neither is a step the user chose: they are
/// artefacts of how `dll_seg`'s cons case is written. Leaving them in the C# means the
/// annotation surface exposes Pulse's unifier.
///
/// The fix is to make the *predicate library* absorb them. A user predicate publishes,
/// for each step a C# body takes, one ghost lemma whose signature mentions only things
/// the C# can name -- parameters, locals, `null`, and spec-level lists. Everything the
/// signature cannot say stays existential *inside* the predicate, and every `rewrite`
/// stays inside the lemma that needs it.

/// `opened p from v prev to_ last l` is `dll_seg p from prev to_ last l` with its first
/// node unfolded: the node's cell is owned outright, and the rest of the segment hangs off
/// its `next` field.
///
/// It names the head node *twice* -- once as the nullable cursor `from` the caller's
/// context and specification already talk about, and once as the box `v` the emitter's
/// field access reads through -- tied by `pure (from == Some v)`. That redundancy is the
/// whole trick: it is what lets a C# call site write `Dll.Open(from, from!, ...)` and get
/// a predicate whose `B.pts_to` is syntactically at `Some?.v var_from`, without ever
/// needing a refined binder `(from: ... { Some? from })` that C# has no way to declare.
unfold
let opened (p: perm) (from: class_DNode__opt) (v: class_DNode)
           (prev: class_DNode__opt) (to_: class_DNode__opt) (last: class_DNode__opt)
           (l: list int)
  : slprop
  = exists* (r: class_DNode__raw) (tl: list int).
      B.pts_to v #p r **
      dll_seg p r.fld_next from to_ last tl **
      pure (from == Some v /\ l == I32.v r.fld_value :: tl /\ r.fld_prev == prev)

/// `cell p v value prev next` is the ownership a freshly allocated node has, stated over
/// the three field values the C# `new DNode { ... }` supplies. Because the emitter's
/// `B.alloc` writes a record *literal*, this folds with no `with` binder at all.
///
/// `value` is the *mathematical* integer, not the machine one: R4.13 sends a C# `int` into
/// a specification as its `.v`, so a predicate a C# `[SpecOp]` can name must be stated that
/// way. The machine value is existential here for exactly that reason, and the `pure` ties
/// the two together.
unfold
let cell (p: perm) (v: class_DNode) (value: int)
         (prev: class_DNode__opt) (next: class_DNode__opt)
  : slprop
  = exists* (x: I32.t).
      B.pts_to v #p ({ fld_value = x; fld_prev = prev; fld_next = next }) **
      pure (I32.v x == value)

/// Open the first node of a non-empty segment. The `rewrite` that moves the segment from
/// the cursor `from` to the box `Some v`, and the one `dll_seg_elim_cons` needs to name
/// the node as `Some?.v from`, are both discharged here and neither escapes.
ghost fn seg_open (p: perm) (from: class_DNode__opt) (v: class_DNode)
    (prev: class_DNode__opt) (to_: class_DNode__opt) (last: class_DNode__opt)
    (#l: list int)
  requires dll_seg p from prev to_ last l ** pure (Cons? l /\ from == Some v)
  ensures  opened p from v prev to_ last l
{
  dll_seg_elim_cons p from prev to_ last #l;
  with r tl. assert (dll_seg p r.fld_next from to_ last tl);
  rewrite (B.pts_to (Some?.v from) #p r) as (B.pts_to v #p r);
}

/// Close the first node again. The segment's left boundary is read off the node's own
/// `prev` field, so a C# body that *wrote* that field simply closes at the new value --
/// which is why `push_front` below needs no obligation of its own for the write.
ghost fn seg_close (p: perm) (from: class_DNode__opt) (v: class_DNode)
    (prev: class_DNode__opt) (to_: class_DNode__opt) (last: class_DNode__opt)
    (l: list int)
  requires opened p from v prev to_ last l
  ensures  dll_seg p from prev to_ last l
{
  with r tl. assert (dll_seg p r.fld_next from to_ last tl);
  rewrite (dll_seg p r.fld_next from to_ last tl)
       as (dll_seg p r.fld_next (Some v) to_ last tl);
  dll_seg_intro_cons p v to_ last #r #tl;
  rewrite (dll_seg p (Some v) r.fld_prev to_ last (I32.v r.fld_value :: tl))
       as (dll_seg p from prev to_ last l);
}

/// Push a node the caller owns outright onto the front of a segment. This is
/// `dll_seg_intro_cons` restated over `cell`, so that its three field values are named
/// rather than projected out of an existential record.
ghost fn seg_cons (p: perm) (v: class_DNode) (value: int)
    (prev: class_DNode__opt) (next: class_DNode__opt)
    (to_: class_DNode__opt) (last: class_DNode__opt)
    (#l: list int)
  requires cell p v value prev next ** dll_seg p next (Some v) to_ last l
  ensures  dll_seg p (Some v) prev to_ last (value :: l)
{
  with x. assert (B.pts_to v #p ({ fld_value = x; fld_prev = prev; fld_next = next }));
  dll_seg_intro_cons p v to_ last
    #({ fld_value = x; fld_prev = prev; fld_next = next }) #l;
  rewrite (dll_seg p (Some v) prev to_ last (I32.v x :: l))
       as (dll_seg p (Some v) prev to_ last (value :: l));
}

// ---------------------------------------------------------------------------
// 6.1 The same two programs, with every proof step a call the C# can make
// ---------------------------------------------------------------------------

/// Compare with `seg_length` in §5: same control flow, same lemma *placement*, but no
/// `with` and no `rewrite`. Every ghost line is a call whose arguments are a parameter, a
/// local, `null`, or the ghost list -- so every one of them is expressible as a C#
/// `[Lemma]` call under §12's style rule.
fn rec seg_length_lemma_style (p: perm) (from: class_DNode__opt) (prev: class_DNode__opt)
    (#l: erased (list int))
  requires dll_seg p from prev None None l ** pure (L.length l < 2147483647)
  returns  n: I32.t
  ensures  dll_seg p from prev None None l ** pure (I32.v n == L.length l)
  decreases (reveal l)
{
  dll_cases p from prev None #l;
  if (None? from) {
    0l
  } else {
    seg_open p from (Some?.v from) prev None None #l;
    let node = B.op_Bang (Some?.v from);
    let rest = seg_length_lemma_style p node.fld_next from;
    seg_close p from (Some?.v from) prev None None l;
    I32.add rest 1l
  }
}

/// Compare with `dll_push_front` in §5: five `rewrite`s, two of them four lines long,
/// become three lemma calls.
fn dll_push_front_lemma_style (head: class_DNode__opt) (tail: class_DNode__opt) (v: I32.t)
    (#l: erased (list int))
  requires is_dll 1.0R head tail l ** pure (Cons? l)
  returns  h: class_DNode__opt
  ensures  is_dll 1.0R h tail (I32.v v :: l)
{
  let n = B.alloc ({ fld_value = v; fld_prev = None; fld_next = head });
  unfold (is_dll 1.0R head tail l);
  dll_cases 1.0R head None tail #l;
  if (None? head) {
    unreachable ()
  } else {
    seg_open 1.0R head (Some?.v head) None None tail #l;
    let t0 = B.op_Bang (Some?.v head);
    B.op_Colon_Equals (Some?.v head) ({ t0 with fld_prev = Some n });
    seg_close 1.0R head (Some?.v head) (Some n) None tail l;
    seg_cons 1.0R n (I32.v v) None head None tail #l;
    fold (is_dll 1.0R (Some n) tail (I32.v v :: l));
    Some n
  }
}
