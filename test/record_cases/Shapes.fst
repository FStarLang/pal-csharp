module Shapes

(** The model of `Shapes.cs`: F* inductives that C# records and an enum denote (§21). *)

type color = | Red | Green | Blue

type shape =
  | Dot : c:color -> shape
  | Bar : length:int -> solid:bool -> shape
  | Pair : left:shape -> right:shape -> shape

let next (c:color) : color =
  match c with Red -> Green | Green -> Blue | Blue -> Red

let shade (s:shape) : option color =
  match s with Dot c -> Some c | _ -> None

let longer (s t:shape) : bool =
  match s, t with
  | Bar n _, Bar m _ -> n < m
  | _ -> false

let first (s:shape) : shape =
  match s with Pair a _ -> a | _ -> s

let solid_bar (s:shape) : option shape =
  match s with Bar n true -> Some (Bar n true) | _ -> None

(** A palette is opaque; picking from one is a function of the color. *)
assume val palette : Type0
assume val pick : palette -> color -> color

let paint (p:palette) (s:shape) : shape =
  match s with Dot c -> Dot (pick p c) | _ -> s

let big_less (a b:int) : bool = a < b
