(** predicate tagged with -1: not precise in defs, 0: not precise but precise in defs, 1: precise*)
open Lib
open Generic

include BasicType with type t = (int * Pred.t)

val equal : t -> t -> bool
(** Compare for equality two predicates. *)

val compare : t -> t -> int

val subst : Subst.t -> t -> t

val precise_tag : t -> bool

val predsym : t -> Predsym.t

val arity : t -> int

val args : t -> Term.t list

val terms : t -> Term.Set.t

val vars : t -> Term.Set.t

val to_string : t -> string

val parse : (t, 'a) MParser.parser

val of_string : string -> t

val unify :
     ?update_check:Unify.Unidirectional.update_check
  -> t Unify.Unidirectional.unifier
(** Unify two predicates. *)

val biunify :
     ?update_check:Unify.Bidirectional.update_check
  -> t Unify.Bidirectional.unifier

val norm : Uf.t -> t -> t
(** Replace all terms with their UF representative. NB this may replace [nil]
    with a variable. *)