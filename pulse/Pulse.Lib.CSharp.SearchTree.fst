module Pulse.Lib.CSharp.SearchTree

/// The comparer-directed searches of a binary search tree whose nodes carry a key and a
/// tag (a red-black tree's colour) (doc/translation.md R27.9). Each function follows the
/// path the code follows, so what it says needs no ordering hypothesis: it is what the
/// search returns, whatever the tree.

module O = Pulse.Lib.CSharp.Order
module T = Pulse.Lib.CSharp.Tree

/// Whether the search for `x` ends at a node whose key compares equal to it.
let rec contains (#a #b: Type0) (c: O.comparer a) (t: T.tree (a & b)) (x: a)
  : Tot bool (decreases t)
  = match t with
    | T.Leaf -> false
    | T.Branch l (v, _) r ->
      let o = O.compare c x v in
      if o = 0 then true else if o < 0 then contains c l x else contains c r x

/// The key the search for `x` ends at, or `d` when it ends at a leaf.
let rec find (#a #b: Type0) (c: O.comparer a) (t: T.tree (a & b)) (x: a) (d: a)
  : Tot a (decreases t)
  = match t with
    | T.Leaf -> d
    | T.Branch l (v, _) r ->
      let o = O.compare c x v in
      if o = 0 then v else if o < 0 then find c l x d else find c r x d

/// The leftmost key, or `d` in the empty tree.
let rec leftmost (#a #b: Type0) (t: T.tree (a & b)) (d: a) : Tot a (decreases t) =
  match t with
  | T.Leaf -> d
  | T.Branch T.Leaf (v, _) _ -> v
  | T.Branch l _ _ -> leftmost l d

/// The rightmost key, or `d` in the empty tree.
let rec rightmost (#a #b: Type0) (t: T.tree (a & b)) (d: a) : Tot a (decreases t) =
  match t with
  | T.Leaf -> d
  | T.Branch _ (v, _) T.Leaf -> v
  | T.Branch _ _ r -> rightmost r d

/// The position of the node the search for `x` ends at, numbering the tree breadth-first
/// as an implicit binary heap is numbered (the root of a subtree being `k`), or -1.
let rec heap_index (#a #b: Type0) (c: O.comparer a) (t: T.tree (a & b)) (x: a) (k: int)
  : Tot int (decreases t)
  = match t with
    | T.Leaf -> -1
    | T.Branch l (v, _) r ->
      let o = O.compare c x v in
      if o = 0 then k
      else if o < 0 then heap_index c l x (2 * k + 1)
      else heap_index c r x (2 * k + 2)
