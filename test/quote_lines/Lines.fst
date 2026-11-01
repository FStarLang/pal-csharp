module Lines

/// The specification side of the quote-line test: a line is a price and an optional cap.

module D = Pulse.Lib.CSharp.Decimal
module L = Pulse.Lib.CSharp.Linq
module Seq = FStar.Seq

type line = { price: D.decimal; cap: option D.decimal }

let line_price (l: line) : D.decimal = l.price
let line_cap (l: line) : option D.decimal = l.cap

let capped (l: line) : bool =
  match l.cap with
  | None -> true
  | Some c -> D.le l.price c

let by_price (s: Seq.seq line) : Seq.seq line = L.sort_by line_price D.le s
