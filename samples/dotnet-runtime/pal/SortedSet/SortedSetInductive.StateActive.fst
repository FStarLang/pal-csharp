module SortedSetInductive.StateActive

module Q = SortedSetInductive.State
module O = SortedSetInductive.Ownership
module C = SortedSetInductive.Cursor
module N = Class_Node
module B = Pulse.Lib.Box
module T = Pulse.Lib.CSharp.Tree
module P = Pulse.Lib.CSharp.RegionPath
module D = Pulse.Lib.CSharp.TopDown
module E = Pulse.Lib.CSharp.RefEq

#set-options "--z3rlimit 10"

let rec present (#a: Type0) (t: O.tree a) (x: N.class_Node__opt a)
  : Lemma (ensures Some? (Q.find_tree t x) <==> O.member t x) (decreases t) =
  match t with
  | T.Leaf -> ()
  | T.Branch l e r ->
    present l x; present r x;
    P.mem_nboxes_branch x l (fst e) (snd e) r;
    Q.find_tree_step l r e x

let as_record (#a: Type0) (t: O.tree a) =
  match t with | T.Leaf -> None | T.Branch l e r -> Some (Q.record l e r)

let rec find_focus (#a: Type0) (t: O.tree a) (x: N.class_Node__opt a)
    (acc: list (D.fr (N.class_Node__raw a) a))
  : Lemma (ensures Q.find_tree t x == as_record (snd (P.focus_acc t x acc))) (decreases t) =
  match t with
  | T.Leaf -> ()
  | T.Branch l (b, v) r ->
    Q.find_tree_step l r (b, v) x;
    P.mem_box_nboxes x l;
    present l x;
    if E.ref_eq b x then ()
    else if P.mem_box x l then
      find_focus l x ({ P.went_right=false; P.fbox=b; P.fval=v; P.fsib=r } :: acc)
    else
      find_focus r x ({ P.went_right=true; P.fbox=b; P.fval=v; P.fsib=l } :: acc)

let rec subtree (#a: Type0) (n: nat) (h: Q.observation a) (t: O.tree a) (x: N.class_Node__opt a)
  : Lemma (requires O.good t /\ (B.is_null x \/ O.member t x) /\
      T.size (P.sub t x) <= n /\
      (forall y. O.member t y ==> Q.find h y == Q.find_tree t y))
      (ensures Q.tree_n n h x == O.lookup t x /\ Q.closed n h x)
      (decreases n) =
  if B.is_null x then C.lookup_root t
  else (
    C.lookup_children t x;
    find_focus t x [];
    let T.Branch l e r = P.sub t x in
    subtree (n - 1) h t (O.top l);
    subtree (n - 1) h t (O.top r))

let active (#a: Type0) (s: O.state a)
  : Lemma (requires O.good (O.active s))
      (ensures Q.tree_at (Q.observe s) (O.top (O.active s)) == O.values (O.active s) /\
        Q.wf (Q.observe s) (O.top (O.active s))) =
  let t = O.active s in
  let at (x: N.class_Node__opt a) : Lemma
      (O.member t x ==> Q.find (Q.observe s) x == Q.find_tree t x) =
    present t x in
  FStar.Classical.forall_intro at;
  C.lookup_root t;
  D.sub_top [] t;
  subtree (Q.fuel (Q.observe s)) (Q.observe s) t (O.top t);
  reveal_opaque (`%Q.tree_at) (Q.tree_at #a);
  reveal_opaque (`%Q.wf) (Q.wf #a)
