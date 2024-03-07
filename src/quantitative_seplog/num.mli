(* A number designed for multiplication with a symbolic heap 
   Syntanctically, it is defined as [number] ^ empty *)

type t = int * int

val get_int : t -> int

val parse : (t, 'a) MParser.parser

val to_string : t -> string

val equal : t -> t -> bool

val subsumed : t -> t -> bool

val compare : t -> t -> int

val hash : t -> int

val empty : t

val is_empty : t -> bool

val mul : t -> t -> t