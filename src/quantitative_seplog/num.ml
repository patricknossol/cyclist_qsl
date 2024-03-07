open Lib
open Symbols
open MParser
open MParser_RE

type t = int * int

let get_int t = fst t

let to_string v = (string_of_int (fst v)) ^ "." ^ (string_of_int (snd v))

let parse s = 
  (regexp (make_regexp "\\d+(\\.\\d*)?") >>= fun digits ->
    spaces >>
    (if String.contains digits '.' then 
      let strs = String.split_on_char '.' digits in
      try_return (fun x -> (int_of_string (Blist.nth x 0), int_of_string (Blist.nth x 1))) strs "Not a valid num" s
    else try_return (fun x -> (int_of_string x, 0)) digits "Not a valid num" s )
    <?> "num") s

let equal n n' = n = n'

let subsumed n n' = n' <= n

let compare n n' = 
  let diff = (fst n) - (fst n') in
  if diff < 0 then -1
  else if diff = 0 then 0
  else 1

let hash n = Int.hash (fst n)

let empty = (-1,0)

let is_empty v = (fst v) = -1

let scale_float_to_int (i, f) =
  if f <= 0 then (i,0) else
  let amount = String.length (string_of_int f) in
  (int_of_string ((string_of_int i) ^ (string_of_int f)), amount)

let mul a b =
  if is_empty b then 
    if is_empty a then empty else a
  else if is_empty a then b
  else 
    let a_int, a_amount = scale_float_to_int a in
    let b_int, b_amount = scale_float_to_int b in
    let res_intstr = string_of_int (a_int * b_int) in
    let amount = a_amount + b_amount in
    if res_intstr = "0" then (0,0) else
    if (String.length res_intstr) - amount = 0 then (0, int_of_string res_intstr) else
    let a = int_of_string (String.sub res_intstr 0 ((String.length res_intstr) - amount)) in
    let b = 
      if amount = 0 then 0
      else 
        int_of_string (String.sub res_intstr ((String.length res_intstr) - amount) amount) in
    (a,b)