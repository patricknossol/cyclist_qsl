(** Multiset of predicates. *)
open Lib
open Generic

include OrderedContainer with type elt = Tpred.t

val equal : t -> t -> bool
(** Test whether the two arguments are the equal *)

val subst : Subst.t -> t -> t

val terms : t -> Term.Set.t

val vars : t -> Term.Set.t

val idents : t -> Predsym.MSet.t
(** Return multiset of identifiers present. *)

val to_string_list : t -> string list

val subsumed : ?total:bool -> Uf.t -> t -> t -> bool
(** Test whether the two arguments are the same modulo the provided equalities.
    Contrary to [subsumed] this includes tags.
    If the optional argument [~total=true] is set to [false] then
    check if the first multiset is a subset of the second modulo equalities. *)

val unify :
     ?total:bool
  -> ?update_check:Unify.Unidirectional.update_check
  -> t Unify.Unidirectional.unifier
(** Compute substitution that makes the two multisets equal up to tags.
- If the optional argument [~total=true] is set to [false] then
  compute substitution that makes the first multiset a subset of the second. *)

val biunify :
     ?total:bool
  -> ?update_check:Unify.Bidirectional.update_check
  -> t Unify.Bidirectional.unifier

val norm : Uf.t -> t -> t
(** Replace all terms with their UF representative. NB this may replace [nil]
    with a variable. *)
