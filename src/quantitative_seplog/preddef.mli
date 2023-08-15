include Lib.BasicType

val mk : Indrule.t list * Predsym.t -> t

val dest : t -> Indrule.t list * Predsym.t

val predsym : t -> Predsym.t

val rules : t -> Indrule.t list

val parse : (t, 'a) MParser.t
