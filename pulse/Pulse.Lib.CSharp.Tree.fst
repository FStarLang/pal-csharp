module Pulse.Lib.CSharp.Tree

/// The model type of a class with two recursive fields (doc/translation.md R10.5).
///
/// `SpecList<T>` needs no module of its own -- F*'s `list` is already the right type, and
/// `FStar.List.Tot` already has the theory. A binary tree has neither, so it lives here.
///
/// This is a *specification* type. It never appears in executable position, so nothing in
/// it is `noeq` for the sake of a runtime representation; `noeq` is here only because the
/// element type is arbitrary and decidable equality on it is not assumed.

module L = FStar.List.Tot

noeq type tree (a: Type0) =
  | Leaf   : tree a
  | Branch : tree a -> a -> tree a -> tree a

let rec size (#a: Type0) (t: tree a) : Tot nat (decreases t) =
  match t with
  | Leaf -> 0
  | Branch l _ r -> 1 + size l + size r

/// The in-order traversal. It is what relates a tree model to a list model, and so what a
/// user's `[Spec]` function reaches for when it wants to say a tree holds the same elements
/// as a list.
let rec elements (#a: Type0) (t: tree a) : Tot (list a) (decreases t) =
  match t with
  | Leaf -> []
  | Branch l v r -> L.append (elements l) (v :: elements r)

/// Binary-search-tree insertion, the model of the destructive operation R10.9 is about.
/// It lives here rather than in a user's `[Spec]` function for the reason §0 rule 3 gives:
/// a proof that needs help gets it from the reusable library or from the user's
/// annotations, and the theory of the model type is the library's half of that.
let rec insert (#a: Type0) (compare: a -> a -> int) (t: tree a) (v: a)
  : Tot (tree a) (decreases t)
  = match t with
    | Leaf -> Branch Leaf v Leaf
    | Branch l hd r ->
      if compare v hd < 0 then Branch (insert compare l v) hd r
      else if compare v hd > 0 then Branch l hd (insert compare r v)
      else Branch l hd r

/// The specialisation `SpecTree<SpecInt>.Insert` denotes: the elements are mathematical
/// integers and the order is theirs.
let insert_int (t: tree int) (v: int) : tree int =
  insert (fun (x y: int) -> if x < y then (-1) else if x > y then 1 else 0) t v

let rec height (#a: Type0) (t: tree a) : Tot nat (decreases t) =
  match t with
  | Leaf -> 0
  | Branch l _ r -> 1 + (if height l > height r then height l else height r)

let rec size_elements (#a: Type0) (t: tree a)
  : Lemma (ensures L.length (elements t) == size t) (decreases t)
          [SMTPat (size t)]
  = match t with
    | Leaf -> ()
    | Branch l v r ->
      size_elements l;
      size_elements r;
      L.append_length (elements l) (v :: elements r)
