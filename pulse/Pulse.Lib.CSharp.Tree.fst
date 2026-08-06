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

/// A keyed entry. The tree above is ordered by whatever order the operation on it is
/// given; a *map* fixes that order at an `int` key carried beside the value, which is what
/// lets a class with an unconstrained type parameter be a search tree at all. C# would
/// order the values with `IComparable<T>`, and a constrained type parameter is refused
/// (PALCS0580, R15.4), so the key is where the order has to live.
noeq type kv (a: Type0) = { kv_key: int; kv_value: a }

let entry (#a: Type0) (key: int) (value: a) : kv a = { kv_key = key; kv_value = value }

let rec kfind (#a: Type0) (t: tree (kv a)) (key: int) : Tot (option a) (decreases t) =
  match t with
  | Leaf -> None
  | Branch l e r ->
    if key < e.kv_key then kfind l key
    else if key > e.kv_key then kfind r key
    else Some e.kv_value

/// Membership and lookup-with-a-default, so that a client can say what it found without a
/// nullable result: `T` is unconstrained, so `null` is not a value of it.
let khas (#a: Type0) (t: tree (kv a)) (key: int) : bool = Some? (kfind t key)

let kget (#a: Type0) (t: tree (kv a)) (key: int) (dflt: a) : a =
  match kfind t key with
  | None -> dflt
  | Some v -> v

let rec kinsert (#a: Type0) (t: tree (kv a)) (key: int) (value: a)
  : Tot (tree (kv a)) (decreases t)
  = match t with
    | Leaf -> Branch Leaf (entry key value) Leaf
    | Branch l e r ->
      if key < e.kv_key then Branch (kinsert l key value) e r
      else if key > e.kv_key then Branch l e (kinsert r key value)
      else Branch l (entry key value) r

/// The keys, in order. Together with `elements` it is how a client relates a map to a list.
let rec kkeys (#a: Type0) (t: tree (kv a)) : Tot (list int) (decreases t) =
  match t with
  | Leaf -> []
  | Branch l e r -> L.append (kkeys l) (e.kv_key :: kkeys r)

/// Insertion never loses a key, and adds at most one. Stated with patterns because the
/// obligation a C# `Insert` leaves is about the tree it returns, not about the recursion
/// that built it.
let rec kinsert_found (#a: Type0) (t: tree (kv a)) (key: int) (value: a)
  : Lemma (ensures kfind (kinsert t key value) key == Some value)
          (decreases t)
          [SMTPat (kfind (kinsert t key value) key)]
  = match t with
    | Leaf -> ()
    | Branch l e r ->
      if key < e.kv_key then kinsert_found l key value
      else if key > e.kv_key then kinsert_found r key value
      else ()

let rec kinsert_size (#a: Type0) (t: tree (kv a)) (key: int) (value: a)
  : Lemma (ensures size (kinsert t key value) ==
                   (if khas t key then size t else size t + 1))
          (decreases t)
          [SMTPat (size (kinsert t key value))]
  = match t with
    | Leaf -> ()
    | Branch l e r ->
      if key < e.kv_key then kinsert_size l key value
      else if key > e.kv_key then kinsert_size r key value
      else ()
