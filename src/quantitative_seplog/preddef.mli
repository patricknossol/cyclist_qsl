(*
Predicate definition
(rules, (symb, (is_precise, conform_predsym_list)))
*)
include Lib.BasicType

val mk : Indrule.t list * (Predsym.t * (Int.t * (Predsym.t list))) -> t

val dest : t -> Indrule.t list * (Predsym.t * (Int.t * (Predsym.t list)))

val predsym : t -> Predsym.t

val is_precise : t -> bool

val is_conform_with : t -> Predsym.t -> bool

val rules : t -> Indrule.t list

val rules_heapsums : (Indrule.t list) -> (Heapsum.t list)

val parse : (t, 'a) MParser.t
