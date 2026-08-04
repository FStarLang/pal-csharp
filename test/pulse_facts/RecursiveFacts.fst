module RecursiveFacts

/// Pinned facts for recursive data structures (doc/translation.md §10).
///
/// Like the other files in `test/pulse_facts`, this is NOT a translation target and NOT a
/// golden file. It is the §0 probe: every shape the §10 emitter is specified to produce is
/// written here *by hand first*, in the emitter's own idiom, and verified. A rule may not
/// be written until the shape it names verifies here.
///
/// The running examples are the three the user asked for: a singly linked list, a doubly
/// linked list, and a binary tree. What they have in common — and what §10 is about — is
/// that the class's ownership predicate cannot be a flat `exists*` over one record. It has
/// to be an *induction*, and the thing it is an induction on is the class's own model.
///
/// The authority for the shape is `Pulse.Lib.LinkedList`, which ships with the toolchain:
/// `is_list` there is `Tot slprop (decreases l)` by cases on the list, with the reference
/// nullable (`option (box node)`) and the *model* driving the recursion. §10 keeps that
/// shape exactly and only renames.

open Pulse

module B = Pulse.Lib.Box
open Pulse.Lib.Box { box, (!), (:=) }
module I32 = FStar.Int32
module L = FStar.List.Tot
module T = FStar.Tactics

#lang-pulse

// ===========================================================================
// 1. The representation of a recursive class (R10.1)
// ===========================================================================

/// R3.7/R3.8, unchanged, except that the record and the reference type are now *mutually*
/// recursive, and the recursive field is nullable.
///
/// F35: a `type … and …` group may mix a record definition with a type abbreviation, so
/// R3.7's record and R3.8's `box` come out as one group and nothing new is needed to tie
/// the knot. This is `Pulse.Lib.LinkedList`'s own `node`/`node_ptr`/`llist`, renamed.
///
/// The C# this stands for is
///
///   public sealed class Node { private int value; private Node? next; }
///
noeq type class_Node__raw = {
  fld_value: I32.t;
  fld_next: class_Node__opt;
}
and class_Node = B.box class_Node__raw

/// R10.2: `Node?` is `option Node`. Nullability is not a refinement of the reference type
/// and not a separate pointer kind — it is F*'s `option`, which is what makes `x == None`
/// the whole of the null test and makes the base case of the induction a *pattern*.
and class_Node__opt = option class_Node

/// R3.9: the model, declared by the user. Here it is a list, because that is what the
/// `[Model]` member returns.
type class_Node__model = list int

// ===========================================================================
// 2. The inductive invariant (R10.3)
// ===========================================================================

/// R10.3. The invariant of a recursive class is a `let rec` over the *nullable* reference,
/// by cases on the model, with `decreases` on the model.
///
/// F36: the recursion has to be on the **model** and not on the reference. A definition by
/// cases on `x` — `None -> …  | Some v -> exists* tl. … inv r.fld_next tl` — has no
/// decreasing measure F* can see, because the sub-model `tl` is related to `m` by a `pure`
/// equation rather than by a pattern. By cases on `m` the sub-model *is* a sub-term, and
/// the definition is accepted with no measure written by the user. This is the single fact
/// that fixes §10's whole shape, and it is why the C# notation of R10.5 asks for the model
/// as a function of the fields: that is exactly the equation being inverted.
///
/// `[@@@mkey]` marks the reference as the key Pulse matches resources on, as
/// `Pulse.Lib.LinkedList` does; without it a goal `class_Node__inv_opt x _ _` would not be
/// found in a context holding it at a different model.
let rec class_Node__inv_opt ([@@@mkey] x: class_Node__opt) (p: perm) (m: class_Node__model)
  : Tot slprop (decreases m)
  = match m with
    | [] -> pure (x == None)
    | hd :: tl ->
      exists* (v: class_Node) (r: class_Node__raw).
        pure (x == Some v) **
        B.pts_to v #p r **
        pure (hd == I32.v r.fld_value) **
        class_Node__inv_opt r.fld_next p tl

/// R10.3a. The *non-null* invariant every §3/§4 rule already talks about is derived, not
/// primitive: a `Node` is a `Node?` that happens to be `Some`. So R4.10's model binders,
/// R4.5's contracts and R3.10b's nested objects need no new case — a recursive class is an
/// ordinary class whose invariant happens to be defined by recursion.
let class_Node__inv (this: class_Node) (#[T.exact (`1.0R)] p: perm) (m: class_Node__model)
  : slprop
  = class_Node__inv_opt (Some this) p m

// ===========================================================================
// 3. The derived case lemmas (R10.4)
// ===========================================================================

/// R10.4. Four ghost lemmas per recursive class, derived from the definition and emitted
/// beside it. They are what a *client* uses; no client ever unfolds the predicate itself,
/// which is what makes R9.17's `.fsti` treatment apply here unchanged.
///
/// This is the point of departure from PAL for C. There, a recursive predicate is written
/// inside `_include_pulse` and each of these lemmas is written by hand in Pulse and invoked
/// by hand with `_ghost_stmt`. Here the predicate is read off the C# `[Model]` member and
/// all four lemmas are generated, so the user writes no Pulse at all.

/// The null test, in the direction the C# `if (n == null)` gives: knowing the reference is
/// null tells you the model is empty.
ghost fn class_Node__nil_case (x: class_Node__opt) (#p: perm) (#m: class_Node__model)
  preserves class_Node__inv_opt x p m
  requires pure (x == None)
  ensures pure (m == [])
{
  match m {
    [] -> { () }
    hd :: tl -> {
      unfold (class_Node__inv_opt x p (hd :: tl));
      with v r. assert (B.pts_to v #p r);
      unreachable ()
    }
  }
}

/// The other direction, and the one that opens R4.10's window: knowing the reference is
/// *not* null gives up the head cell and the tail's invariant.
ghost fn class_Node__elim_cons (x: class_Node__opt { Some? x }) (#p: perm) (#m: class_Node__model)
  requires class_Node__inv_opt x p m
  ensures exists* (r: class_Node__raw) (tl: class_Node__model).
    B.pts_to (Some?.v x) #p r **
    class_Node__inv_opt r.fld_next p tl **
    pure (m == I32.v r.fld_value :: tl)
{
  match m {
    [] -> {
      unfold (class_Node__inv_opt x p []);
      unreachable ()
    }
    hd :: tl -> {
      unfold (class_Node__inv_opt x p (hd :: tl));
      with v r. assert (B.pts_to v #p r);
      rewrite each v as (Some?.v x);
      ()
    }
  }
}

/// Closing the window again.
ghost fn class_Node__intro_cons (x: class_Node__opt { Some? x })
    (#p: perm) (#r: class_Node__raw) (#tl: class_Node__model)
  requires B.pts_to (Some?.v x) #p r ** class_Node__inv_opt r.fld_next p tl
  ensures class_Node__inv_opt x p (I32.v r.fld_value :: tl)
{
  fold (class_Node__inv_opt (Some (Some?.v x)) p (I32.v r.fld_value :: tl));
  rewrite (class_Node__inv_opt (Some (Some?.v x)) p (I32.v r.fld_value :: tl))
       as (class_Node__inv_opt x p (I32.v r.fld_value :: tl));
}

/// R10.4b. The *consuming* form of the null test. `nil_case` preserves the invariant,
/// which is what a method whose postcondition still owes it needs; a method that consumes
/// its argument (R10.6b's `Append` moves `x` into its result) needs to give it up instead.
/// Which one the emitter uses is read off the contract, exactly as R4.10 already reads it.
ghost fn class_Node__elim_nil (x: class_Node__opt) (#p: perm) (#m: class_Node__model)
  requires class_Node__inv_opt x p m ** pure (x == None)
  ensures pure (m == [])
{
  class_Node__nil_case x;
  unfold (class_Node__inv_opt x p []);
}

/// The empty list owns nothing, which is what makes `Node? n = null;` free.
ghost fn class_Node__intro_nil (x: class_Node__opt) (p: perm)
  requires pure (x == None)
  ensures class_Node__inv_opt x p []
{
  fold (class_Node__inv_opt x p [])
}

/// R10.4a. The equivalence a client needs *before* it has tested anything: the shape of
/// the model and the nullity of the reference determine each other. This is what lets a
/// C# `if (n == null)` be a proof step at all — in the `else` branch it is what tells the
/// prover the model is a `Cons`, and hence that `elim_cons` applies.
ghost fn class_Node__cases (x: class_Node__opt) (#p: perm) (#m: class_Node__model)
  preserves class_Node__inv_opt x p m
  ensures pure (Some? x <==> Cons? m)
{
  match m {
    [] -> {
      unfold (class_Node__inv_opt x p []);
      fold (class_Node__inv_opt x p []);
    }
    hd :: tl -> {
      unfold (class_Node__inv_opt x p (hd :: tl));
      with v r. assert (B.pts_to v #p r);
      fold (class_Node__inv_opt x p (hd :: tl));
    }
  }
}

// ===========================================================================
// 4. Clients (R10.6): recursive methods over a recursive class
// ===========================================================================

/// The C# these stand for is an ordinary static class over a nullable reference:
///
///   public static class Lists
///   {
///       [Requires("n.Items.Length < 2147483647")]
///       [Ensures("Result == n.Items.Length")]
///       [Decreases("n.Items")]
///       public static int Length(Node? n)
///       {
///           if (n == null) return 0;
///           return 1 + Length(n.next);
///       }
///   }
///
/// Everything below is in the emitter's idiom, A-normalised, with `unfold`/`fold` replaced
/// by the R10.4 lemmas. Nothing here is hand-optimised.

/// F37: the case lemmas are placed by the *null test the C# already writes*. R4.10 opens a
/// window around a field access; R10.6 opens the same window around the `else` branch of a
/// null test, with `elim_cons` at the top and `intro_cons` at the bottom. So the user never
/// invokes a lemma — the `if (n == null)` they had to write anyway is the ghost step.
///
/// F38: `decreases` on the *erased model* is accepted, and `tl << pre_n` is discharged by
/// SMT from the `pure (pre_n == hd :: tl)` that `elim_cons` hands back. No user measure and
/// no `[Decreases]` on the tail is needed beyond naming the model.
fn rec func_Lists_Length (var_n: class_Node__opt) (#pre_n: erased class_Node__model)
  requires class_Node__inv_opt var_n 1.0R pre_n **
           pure (L.length pre_n < 2147483647)
  returns  var_result: I32.t
  ensures  class_Node__inv_opt var_n 1.0R pre_n **
           pure ((I32.v var_result) == L.length pre_n)
  decreases reveal pre_n
{
  class_Node__cases var_n;
  if (None? var_n) {
    class_Node__nil_case var_n;
    0l
  } else {
    class_Node__elim_cons var_n;
    let t0 = B.op_Bang (Some?.v var_n);
    let t1 = func_Lists_Length t0.fld_next;
    let t2 = (I32.add t1 1l);
    class_Node__intro_cons var_n;
    t2
  }
}

/// R10.6a: allocation. This is the body of `Node`'s constructor, and the one place a new
/// cell enters the induction. `intro_cons` is the whole of the proof; the emitter needs no
/// new rule, because `new Node(v, n)` already transfers `n`'s invariant into the field by
/// R3.10b, and R10.4's intro is R3.10b's `fold`.
///
///   public static Node Cons(int v, Node? n) => new Node(v, n);
fn func_Lists_Cons (var_v: I32.t) (var_n: class_Node__opt) (#pre_n: erased class_Node__model)
  requires class_Node__inv_opt var_n 1.0R pre_n
  returns  var_result: class_Node__opt
  ensures  class_Node__inv_opt var_result 1.0R ((I32.v var_v) :: pre_n)
{
  let t0 = B.alloc ({ fld_value = var_v; fld_next = var_n });
  class_Node__intro_cons (Some t0);
  Some t0
}

/// R10.6b: destructive traversal. `Append` walks to the end of `x` and writes `y` into the
/// last `next` field, which is the case every flat-`exists*` invariant cannot express and
/// the reason §10 exists at all.
///
///   [Decreases("x.Items")]
///   public static Node? Append(Node? x, Node? y)
///   {
///       if (x == null) return y;
///       x.next = Append(x.next, y);
///       return x;
///   }
///
/// F39: the emitter's ordinary field-write idiom (`B.op_Colon_Equals var ({ t with … })`,
/// R3.12) composes with R10.4 unchanged. The window opened by the null test is exactly the
/// window R3.12 needs.
fn rec func_Lists_Append (var_x: class_Node__opt) (var_y: class_Node__opt)
    (#pre_x: erased class_Node__model) (#pre_y: erased class_Node__model)
  requires class_Node__inv_opt var_x 1.0R pre_x **
           class_Node__inv_opt var_y 1.0R pre_y
  returns  var_result: class_Node__opt
  ensures  class_Node__inv_opt var_result 1.0R (L.append pre_x pre_y)
  decreases reveal pre_x
{
  class_Node__cases var_x;
  if (None? var_x) {
    class_Node__elim_nil var_x;
    var_y
  } else {
    class_Node__elim_cons var_x;
    let t0 = B.op_Bang (Some?.v var_x);
    let t1 = func_Lists_Append t0.fld_next var_y;
    let t2 = B.op_Bang (Some?.v var_x);
    B.op_Colon_Equals (Some?.v var_x) ({ t2 with fld_next = t1 });
    class_Node__intro_cons var_x;
    var_x
  }
}

// ===========================================================================
// 5. Sharing a recursive invariant (R10.7)
// ===========================================================================

/// R3.10c emits `__inv_share` / `__inv_gather` for every class, so that `[Frac]` and
/// read-only aliasing work. For a recursive class those two are themselves recursive
/// ghost functions, which is the only thing R10.7 has to say.
///
/// F40: a `ghost fn rec` may recurse on an *erased* model. `decreases m` on an implicit
/// ghost binder is accepted, so the emitter's existing share/gather template needs only
/// the `rec` keyword and a `decreases` line.
ghost fn rec class_Node__inv_opt_share (x: class_Node__opt) (#p: perm) (#m: class_Node__model)
  requires class_Node__inv_opt x p m
  ensures class_Node__inv_opt x (p /. 2.0R) m ** class_Node__inv_opt x (p /. 2.0R) m
  decreases m
{
  class_Node__cases x;
  if (None? x) {
    class_Node__elim_nil x;
    class_Node__intro_nil x (p /. 2.0R);
    class_Node__intro_nil x (p /. 2.0R);
  } else {
    class_Node__elim_cons x;
    with r tl. assert (B.pts_to (Some?.v x) #p r ** class_Node__inv_opt r.fld_next p tl);
    B.share (Some?.v x);
    class_Node__inv_opt_share r.fld_next #p #tl;
    class_Node__intro_cons x #(p /. 2.0R) #r #tl;
    class_Node__intro_cons x #(p /. 2.0R) #r #tl;
  }
}

/// F41: gather is the same shape, and needs `[@@allow_ambiguous]` for exactly the reason
/// R3.10c already documents -- two copies of the same predicate at different models.
[@@allow_ambiguous]
ghost fn rec class_Node__inv_opt_gather (x: class_Node__opt) (p q: perm)
    (#m #alt_m: class_Node__model)
  requires class_Node__inv_opt x p m ** class_Node__inv_opt x q alt_m
  ensures class_Node__inv_opt x (p +. q) m ** pure (m == alt_m)
  decreases m
{
  class_Node__cases x #p #m;
  class_Node__cases x #q #alt_m;
  if (None? x) {
    class_Node__elim_nil x #p #m;
    class_Node__elim_nil x #q #alt_m;
    class_Node__intro_nil x (p +. q);
  } else {
    class_Node__elim_cons x #p #m;
    with r tl. assert (B.pts_to (Some?.v x) #p r ** class_Node__inv_opt r.fld_next p tl);
    class_Node__elim_cons x #q #alt_m;
    with r2 tl2. assert (B.pts_to (Some?.v x) #q r2 ** class_Node__inv_opt r2.fld_next q tl2);
    B.gather (Some?.v x);
    rewrite each r2 as r;
    class_Node__inv_opt_gather r.fld_next p q #tl #tl2;
    class_Node__intro_cons x #(p +. q) #r #tl;
  }
}

// ===========================================================================
// 6. A wrapper class holding a recursive field (R10.8)
// ===========================================================================

/// F42: R3.10b -- "a field of class type contributes that class's invariant at an
/// existentially bound model" -- applies verbatim when the field's type is *nullable and
/// recursive*. The only change is that the contributed predicate is `__inv_opt` rather
/// than `__inv`. So the ordinary M2 class rules cover the handle class for free, and §10
/// is confined to the recursive class itself.
///
///   public sealed class LinkedList
///   {
///       private Node? head;
///       [Model] private SpecList<SpecInt> Items => head.Items;
///
///       [Ensures("Items == SpecList.Cons(v, Old(Items))")]
///       public void Push(int v) { head = new Node(v, head); }
///
///       [Requires("Items.Length < 2147483647")]
///       [Ensures("Result == Items.Length")]
///       public int Count() => Lists.Length(head);
///   }
noeq type class_LinkedList__raw = { fld_head: class_Node__opt }

let class_LinkedList = B.box class_LinkedList__raw

type class_LinkedList__model = list int

let class_LinkedList__inv (this: class_LinkedList) (#[T.exact (`1.0R)] p: perm)
    (m: class_LinkedList__model) : slprop
  = exists* (r: class_LinkedList__raw) (m_head: class_Node__model).
      B.pts_to this #p r **
      class_Node__inv_opt r.fld_head p m_head **
      pure (m == m_head)

fn func_LinkedList__ctor (_: unit)
  requires emp
  returns  var_this: class_LinkedList
  ensures  class_LinkedList__inv var_this []
{
  class_Node__intro_nil None 1.0R;
  let t0 = B.alloc ({ fld_head = None });
  fold (class_LinkedList__inv t0 #1.0R []);
  t0
}

fn func_LinkedList_Push (var_this: class_LinkedList) (var_v: I32.t)
    (#pre_this: erased class_LinkedList__model)
  requires class_LinkedList__inv var_this pre_this
  ensures  exists* post_this.
           class_LinkedList__inv var_this post_this **
           pure (post_this == (I32.v var_v) :: pre_this)
{
  unfold (class_LinkedList__inv var_this #1.0R pre_this);
  let t0 = B.op_Bang var_this;
  let t1 = func_Lists_Cons var_v t0.fld_head;
  let t2 = B.op_Bang var_this;
  B.op_Colon_Equals var_this ({ t2 with fld_head = t1 });
  fold (class_LinkedList__inv var_this #1.0R ((I32.v var_v) :: pre_this));
}

fn func_LinkedList_Count (var_this: class_LinkedList) (#pre_this: erased class_LinkedList__model)
  requires class_LinkedList__inv var_this pre_this **
           pure (L.length pre_this < 2147483647)
  returns  var_result: I32.t
  ensures  class_LinkedList__inv var_this pre_this **
           pure ((I32.v var_result) == L.length pre_this)
{
  unfold (class_LinkedList__inv var_this #1.0R pre_this);
  let t0 = B.op_Bang var_this;
  let t1 = func_Lists_Length t0.fld_head;
  fold (class_LinkedList__inv var_this #1.0R pre_this);
  t1
}

// ===========================================================================
// 7. Binary trees (R10.9): two recursive occurrences
// ===========================================================================

/// The list case has one recursive field. A tree has two, and the question §10 has to
/// answer is whether anything changes. F43: nothing does. The recursion is still on the
/// model, the model's constructor still has one sub-model per recursive field, and the
/// two sub-invariants sit side by side under `**` -- which is exactly what makes the two
/// subtrees separately owned, and hence what makes an in-place tree insert verifiable.
///
/// `spec_tree` is the model type. In the shipped library it is `SpecTree<T>` in
/// `Pal.Annotations`, mapping to `Pulse.Lib.CSharp.Tree.tree`; here it is local to the
/// probe.
noeq type spec_tree (a: Type0) =
  | Leaf   : spec_tree a
  | Branch : spec_tree a -> a -> spec_tree a -> spec_tree a

///   public sealed class TreeNode
///   {
///       private int value;
///       private TreeNode? left;
///       private TreeNode? right;
///       [Model] private SpecTree<SpecInt> Contents =>
///           SpecTree.Branch(left.Contents, value, right.Contents);
///   }
noeq type class_TreeNode__raw = {
  fld_value: I32.t;
  fld_left: class_TreeNode__opt;
  fld_right: class_TreeNode__opt;
}
and class_TreeNode = B.box class_TreeNode__raw
and class_TreeNode__opt = option class_TreeNode

type class_TreeNode__model = spec_tree int

let rec class_TreeNode__inv_opt ([@@@mkey] x: class_TreeNode__opt) (p: perm)
    (m: class_TreeNode__model)
  : Tot slprop (decreases m)
  = match m with
    | Leaf -> pure (x == None)
    | Branch ml hd mr ->
      exists* (v: class_TreeNode) (r: class_TreeNode__raw).
        pure (x == Some v) **
        B.pts_to v #p r **
        pure (hd == I32.v r.fld_value) **
        class_TreeNode__inv_opt r.fld_left p ml **
        class_TreeNode__inv_opt r.fld_right p mr

let class_TreeNode__inv (this: class_TreeNode) (#[T.exact (`1.0R)] p: perm)
    (m: class_TreeNode__model) : slprop
  = class_TreeNode__inv_opt (Some this) p m

ghost fn class_TreeNode__leaf_case (x: class_TreeNode__opt) (#p: perm) (#m: class_TreeNode__model)
  preserves class_TreeNode__inv_opt x p m
  requires pure (x == None)
  ensures pure (m == Leaf)
{
  match m {
    Leaf -> { () }
    Branch ml hd mr -> {
      unfold (class_TreeNode__inv_opt x p (Branch ml hd mr));
      with v r. assert (B.pts_to v #p r);
      unreachable ()
    }
  }
}

ghost fn class_TreeNode__elim_leaf (x: class_TreeNode__opt) (#p: perm) (#m: class_TreeNode__model)
  requires class_TreeNode__inv_opt x p m ** pure (x == None)
  ensures pure (m == Leaf)
{
  class_TreeNode__leaf_case x;
  unfold (class_TreeNode__inv_opt x p Leaf);
}

ghost fn class_TreeNode__intro_leaf (x: class_TreeNode__opt) (p: perm)
  requires pure (x == None)
  ensures class_TreeNode__inv_opt x p Leaf
{
  fold (class_TreeNode__inv_opt x p Leaf)
}

ghost fn class_TreeNode__elim_branch (x: class_TreeNode__opt { Some? x }) (#p: perm)
    (#m: class_TreeNode__model)
  requires class_TreeNode__inv_opt x p m
  ensures exists* (r: class_TreeNode__raw) (ml mr: class_TreeNode__model).
    B.pts_to (Some?.v x) #p r **
    class_TreeNode__inv_opt r.fld_left p ml **
    class_TreeNode__inv_opt r.fld_right p mr **
    pure (m == Branch ml (I32.v r.fld_value) mr)
{
  match m {
    Leaf -> {
      unfold (class_TreeNode__inv_opt x p Leaf);
      unreachable ()
    }
    Branch ml hd mr -> {
      unfold (class_TreeNode__inv_opt x p (Branch ml hd mr));
      with v r. assert (B.pts_to v #p r);
      rewrite each v as (Some?.v x);
      ()
    }
  }
}

ghost fn class_TreeNode__intro_branch (x: class_TreeNode__opt { Some? x }) (#p: perm)
    (#r: class_TreeNode__raw) (#ml #mr: class_TreeNode__model)
  requires B.pts_to (Some?.v x) #p r **
           class_TreeNode__inv_opt r.fld_left p ml **
           class_TreeNode__inv_opt r.fld_right p mr
  ensures class_TreeNode__inv_opt x p (Branch ml (I32.v r.fld_value) mr)
{
  fold (class_TreeNode__inv_opt (Some (Some?.v x)) p (Branch ml (I32.v r.fld_value) mr));
  rewrite (class_TreeNode__inv_opt (Some (Some?.v x)) p (Branch ml (I32.v r.fld_value) mr))
       as (class_TreeNode__inv_opt x p (Branch ml (I32.v r.fld_value) mr));
}

ghost fn class_TreeNode__cases (x: class_TreeNode__opt) (#p: perm) (#m: class_TreeNode__model)
  preserves class_TreeNode__inv_opt x p m
  ensures pure (Some? x <==> Branch? m)
{
  match m {
    Leaf -> {
      unfold (class_TreeNode__inv_opt x p Leaf);
      fold (class_TreeNode__inv_opt x p Leaf);
    }
    Branch ml hd mr -> {
      unfold (class_TreeNode__inv_opt x p (Branch ml hd mr));
      with v r. assert (B.pts_to v #p r);
      fold (class_TreeNode__inv_opt x p (Branch ml hd mr));
    }
  }
}

/// The `[Spec]` model functions, `Let_*.fst` in R4.2's scheme.
let rec spec_Trees_Size (m: class_TreeNode__model) : Tot nat (decreases m) =
  match m with
  | Leaf -> 0
  | Branch ml _ mr -> 1 + spec_Trees_Size ml + spec_Trees_Size mr

let rec spec_Trees_Insert (m: class_TreeNode__model) (v: int)
  : Tot class_TreeNode__model (decreases m)
  = match m with
    | Leaf -> Branch Leaf v Leaf
    | Branch ml hd mr ->
      if v < hd then Branch (spec_Trees_Insert ml v) hd mr
      else if v > hd then Branch ml hd (spec_Trees_Insert mr v)
      else Branch ml hd mr

///   [Requires("t.Contents.Size < 2147483647")]
///   [Ensures("Result == t.Contents.Size")]
///   [Decreases("t.Contents")]
///   public static int Size(TreeNode? t)
///   {
///       if (t == null) return 0;
///       return 1 + Size(t.left) + Size(t.right);
///   }
fn rec func_Trees_Size (var_t: class_TreeNode__opt) (#pre_t: erased class_TreeNode__model)
  requires class_TreeNode__inv_opt var_t 1.0R pre_t **
           pure (spec_Trees_Size pre_t < 2147483647)
  returns  var_result: I32.t
  ensures  class_TreeNode__inv_opt var_t 1.0R pre_t **
           pure ((I32.v var_result) == spec_Trees_Size pre_t)
  decreases reveal pre_t
{
  class_TreeNode__cases var_t;
  if (None? var_t) {
    class_TreeNode__leaf_case var_t;
    0l
  } else {
    class_TreeNode__elim_branch var_t;
    let t0 = B.op_Bang (Some?.v var_t);
    let t1 = func_Trees_Size t0.fld_left;
    let t2 = func_Trees_Size t0.fld_right;
    let t3 = (I32.add (I32.add 1l t1) t2);
    class_TreeNode__intro_branch var_t;
    t3
  }
}

/// The destructive one: an in-place BST insert. This is R10.9's real content -- the write
/// happens to one subtree's field while the *other* subtree's invariant sits untouched in
/// the context, which is precisely what separating conjunction buys.
///
///   [Ensures("Result.Contents == Trees.SpecInsert(t.Contents, v)")]
///   [Decreases("t.Contents")]
///   public static TreeNode? Insert(TreeNode? t, int v)
///   {
///       if (t == null) return new TreeNode(v, null, null);
///       if (v < t.value)      t.left  = Insert(t.left, v);
///       else if (v > t.value) t.right = Insert(t.right, v);
///       return t;
///   }
fn rec func_Trees_Insert (var_t: class_TreeNode__opt) (var_v: I32.t)
    (#pre_t: erased class_TreeNode__model)
  requires class_TreeNode__inv_opt var_t 1.0R pre_t
  returns  var_result: class_TreeNode__opt
  ensures  class_TreeNode__inv_opt var_result 1.0R (spec_Trees_Insert pre_t (I32.v var_v))
  decreases reveal pre_t
{
  class_TreeNode__cases var_t;
  if (None? var_t) {
    class_TreeNode__elim_leaf var_t;
    let t0 = B.alloc ({ fld_value = var_v; fld_left = None; fld_right = None });
    class_TreeNode__intro_leaf None 1.0R;
    class_TreeNode__intro_leaf None 1.0R;
    class_TreeNode__intro_branch (Some t0);
    Some t0
  } else {
    class_TreeNode__elim_branch var_t;
    let t1 = B.op_Bang (Some?.v var_t);
    if (I32.lt var_v t1.fld_value) {
      let t2 = func_Trees_Insert t1.fld_left var_v;
      let t3 = B.op_Bang (Some?.v var_t);
      B.op_Colon_Equals (Some?.v var_t) ({ t3 with fld_left = t2 });
      class_TreeNode__intro_branch var_t;
      var_t
    } else {
      if (I32.gt var_v t1.fld_value) {
        let t4 = func_Trees_Insert t1.fld_right var_v;
        let t5 = B.op_Bang (Some?.v var_t);
        B.op_Colon_Equals (Some?.v var_t) ({ t5 with fld_right = t4 });
        class_TreeNode__intro_branch var_t;
        var_t
      } else {
        class_TreeNode__intro_branch var_t;
        var_t
      }
    }
  }
}

// ===========================================================================
// 8. Doubly linked lists (R10.10): a back pointer
// ===========================================================================

/// A `prev` field breaks the rule §10 rests on. `next` is *owned* -- the cell it points at
/// belongs to this list and to nothing else -- but `prev` points at a cell that already
/// belongs to the list, so owning it too would be owning it twice. The predicate cannot be
/// a function of the fields alone.
///
/// F44: the standard answer works unchanged in the emitter's idiom -- the predicate takes
/// the predecessor as an extra *index*, and the back pointer is constrained, not owned:
/// `pure (r.fld_prev == left)`, with the recursive call passing `x` as the new `left`.
///
/// R10.10's surface rule: a field marked `[Backward]` is not owned. It contributes one
/// index to the class's invariant and one pure equation to each node, and every method
/// over the class gains one erased implicit for it. Exactly one `[Backward]` field is
/// allowed per class, and its type must be the class's own nullable type -- anything else
/// is refused, because the derivation below is the only one we have pinned.
///
///   public sealed class DNode
///   {
///       private int value;
///       [Backward] private DNode? prev;
///       private DNode? next;
///       [Model] private SpecList<SpecInt> Items => SpecList.Cons(value, next.Items);
///   }
noeq type class_DNode__raw = {
  fld_value: I32.t;
  fld_prev: class_DNode__opt;
  fld_next: class_DNode__opt;
}
and class_DNode = B.box class_DNode__raw
and class_DNode__opt = option class_DNode

type class_DNode__model = list int

let rec class_DNode__inv_opt (left: class_DNode__opt) ([@@@mkey] x: class_DNode__opt)
    (p: perm) (m: class_DNode__model)
  : Tot slprop (decreases m)
  = match m with
    | [] -> pure (x == None)
    | hd :: tl ->
      exists* (v: class_DNode) (r: class_DNode__raw).
        pure (x == Some v) **
        B.pts_to v #p r **
        pure (hd == I32.v r.fld_value /\ r.fld_prev == left) **
        class_DNode__inv_opt x r.fld_next p tl

ghost fn class_DNode__nil_case (left: class_DNode__opt) (x: class_DNode__opt)
    (#p: perm) (#m: class_DNode__model)
  preserves class_DNode__inv_opt left x p m
  requires pure (x == None)
  ensures pure (m == [])
{
  match m {
    [] -> { () }
    hd :: tl -> {
      unfold (class_DNode__inv_opt left x p (hd :: tl));
      with v r. assert (B.pts_to v #p r);
      unreachable ()
    }
  }
}

ghost fn class_DNode__elim_nil (left: class_DNode__opt) (x: class_DNode__opt)
    (#p: perm) (#m: class_DNode__model)
  requires class_DNode__inv_opt left x p m ** pure (x == None)
  ensures pure (m == [])
{
  class_DNode__nil_case left x;
  unfold (class_DNode__inv_opt left x p []);
}

ghost fn class_DNode__intro_nil (left: class_DNode__opt) (x: class_DNode__opt) (p: perm)
  requires pure (x == None)
  ensures class_DNode__inv_opt left x p []
{
  fold (class_DNode__inv_opt left x p [])
}

ghost fn class_DNode__elim_cons (left: class_DNode__opt) (x: class_DNode__opt { Some? x })
    (#p: perm) (#m: class_DNode__model)
  requires class_DNode__inv_opt left x p m
  ensures exists* (r: class_DNode__raw) (tl: class_DNode__model).
    B.pts_to (Some?.v x) #p r **
    class_DNode__inv_opt x r.fld_next p tl **
    pure (m == I32.v r.fld_value :: tl /\ r.fld_prev == left)
{
  match m {
    [] -> {
      unfold (class_DNode__inv_opt left x p []);
      unreachable ()
    }
    hd :: tl -> {
      unfold (class_DNode__inv_opt left x p (hd :: tl));
      with v r. assert (B.pts_to v #p r);
      rewrite each v as (Some?.v x);
      ()
    }
  }
}

/// The predecessor is *read off the field*, not passed in. That is what makes a write to
/// `prev` a legal proof step: after `head.prev = n`, re-introducing the cons yields the
/// invariant at the new predecessor with no extra obligation.
ghost fn class_DNode__intro_cons (x: class_DNode__opt { Some? x }) (#p: perm)
    (#r: class_DNode__raw) (#tl: class_DNode__model)
  requires B.pts_to (Some?.v x) #p r ** class_DNode__inv_opt x r.fld_next p tl
  ensures class_DNode__inv_opt r.fld_prev x p (I32.v r.fld_value :: tl)
{
  fold (class_DNode__inv_opt r.fld_prev (Some (Some?.v x)) p (I32.v r.fld_value :: tl));
  rewrite (class_DNode__inv_opt r.fld_prev (Some (Some?.v x)) p (I32.v r.fld_value :: tl))
       as (class_DNode__inv_opt r.fld_prev x p (I32.v r.fld_value :: tl));
}

ghost fn class_DNode__cases (left: class_DNode__opt) (x: class_DNode__opt)
    (#p: perm) (#m: class_DNode__model)
  preserves class_DNode__inv_opt left x p m
  ensures pure (Some? x <==> Cons? m)
{
  match m {
    [] -> {
      unfold (class_DNode__inv_opt left x p []);
      fold (class_DNode__inv_opt left x p []);
    }
    hd :: tl -> {
      unfold (class_DNode__inv_opt left x p (hd :: tl));
      with v r. assert (B.pts_to v #p r);
      fold (class_DNode__inv_opt left x p (hd :: tl));
    }
  }
}

/// F45: a method over a `[Backward]`-bearing class gains one erased implicit for the index.
/// It is solved by unification at every call site, including the recursive one, where the
/// caller's `var_n` becomes the callee's predecessor -- so the user writes nothing.
///
///   [Requires("n.Items.Length < 2147483647")]
///   [Ensures("Result == n.Items.Length")]
///   [Decreases("n.Items")]
///   public static int Length(DNode? n)
///   {
///       if (n == null) return 0;
///       return 1 + Length(n.next);
///   }
fn rec func_DLists_Length (var_n: class_DNode__opt)
    (#g_prev: erased class_DNode__opt) (#pre_n: erased class_DNode__model)
  requires class_DNode__inv_opt g_prev var_n 1.0R pre_n **
           pure (L.length pre_n < 2147483647)
  returns  var_result: I32.t
  ensures  class_DNode__inv_opt g_prev var_n 1.0R pre_n **
           pure ((I32.v var_result) == L.length pre_n)
  decreases reveal pre_n
{
  class_DNode__cases g_prev var_n;
  if (None? var_n) {
    class_DNode__nil_case g_prev var_n;
    0l
  } else {
    class_DNode__elim_cons g_prev var_n;
    let t0 = B.op_Bang (Some?.v var_n);
    let t1 = func_DLists_Length t0.fld_next;
    let t2 = (I32.add t1 1l);
    class_DNode__intro_cons var_n;
    t2
  }
}

/// The operation that justifies the whole design: a front insertion, which must *write*
/// the old head's back pointer. The write is an ordinary R3.12 field update; what makes it
/// verify is that `elim_cons`/`intro_cons` read the predecessor index off the field.
///
///   [Ensures("Result.Items == SpecList.Cons(v, head.Items)")]
///   public static DNode PushFront(DNode? head, int v)
///   {
///       DNode n = new DNode(v, null, head);
///       if (head != null) head.prev = n;
///       return n;
///   }
fn func_DLists_PushFront (var_head: class_DNode__opt) (var_v: I32.t)
    (#pre_head: erased class_DNode__model)
  requires class_DNode__inv_opt None var_head 1.0R pre_head
  returns  var_result: class_DNode__opt
  ensures  class_DNode__inv_opt None var_result 1.0R ((I32.v var_v) :: pre_head)
{
  let t0 = B.alloc ({ fld_value = var_v; fld_prev = None; fld_next = var_head });
  class_DNode__cases None var_head;
  if (None? var_head) {
    class_DNode__elim_nil None var_head;
    class_DNode__intro_nil (Some t0) var_head 1.0R;
    class_DNode__intro_cons (Some t0);
    Some t0
  } else {
    class_DNode__elim_cons None var_head;
    let t1 = B.op_Bang (Some?.v var_head);
    B.op_Colon_Equals (Some?.v var_head) ({ t1 with fld_prev = Some t0 });
    class_DNode__intro_cons var_head;
    class_DNode__intro_cons (Some t0);
    Some t0
  }
}
