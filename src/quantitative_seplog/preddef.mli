include Lib.BasicType

val mk : Indrule.t list * (Predsym.t * Int.t) -> t

val dest : t -> Indrule.t list * (Predsym.t * Int.t)

val predsym : t -> Predsym.t

val is_conform : t -> bool

val rules : t -> Indrule.t list

val parse : (t, 'a) MParser.t
