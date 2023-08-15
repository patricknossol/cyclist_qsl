open Lib
open Symbols
open MParser

type t = float

let to_string v = string_of_float v

let parse st = (*TODO klappt nicht fuer floats*)
    ( many1_chars digit |>> float_of_string <?> "num" ) st

let equal n n' = n = n'

let subsumed n n' = n' <= n

let compare n n' = 
  let diff = n -. n' in
  if diff < 0. then -1
  else if diff = 0. then 0
  else 1

let hash n = Float.hash n

let empty = -1.

let is_empty v = v = -1.

let add a b =
  if is_empty b then
    if is_empty a then empty else a
  else if is_empty a then b
  else a +. b

let sub a b =
  if is_empty b then a
  else if is_empty a then empty
  else if a -. b < 0. then empty
  else a -. b

let mul a b =
  if is_empty b then 
    if is_empty a then empty else a
  else if is_empty a then b
  else a *. b