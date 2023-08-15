(** Inductive rule type consisting of a symbolic heap and a predicate head. *)

open Lib
open Generic

include BasicType

val mk : Heapsum.t -> Pred.t -> t

val dest : t -> Heapsum.t * Pred.t

val vars : t -> Term.Set.t

val predsym : t -> Predsym.t

val arity : t -> int

val formals : t -> Term.t list

val body : t -> Heapsum.t

val freshen : Term.Set.t -> t -> t
(** Replace all variables in rule such that they are disjoint with the set 
    provided. *)

val subst : Subst.t -> t -> t

val parse : (t, 'a) MParser.t

val unfold :
  ?gen_tags:bool -> Term.Set.t * Tags.t -> Tpred.t -> t -> Heapsum.t
(** [unfold (vs, ts) p r] returns the body of the inductive rule [r] with:
      the formal parameters replaced by the arguments of [p]; 
      the remaining variables freshened, avoiding those in [vs]; and
      the predicates assigned fresh existential tags avoiding those in [ts],
        unless the optional argument [gen_tags=true] is set to false.
    NB. This assumes that all predicates in the body of [r] are untagged.
*)