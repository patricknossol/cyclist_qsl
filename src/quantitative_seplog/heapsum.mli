(** A sum over symbolic heaps. *)

open Lib
open Generic

include BasicType with type t = Heap.t list

exception Not_symheap

val empty : t
(** An empty heapsum. *)

val is_empty: t -> bool

val dest : t -> Heap.t
(** Return the single summand, if there is exactly one, else raise [Not_symheap]. *)

val equal : t -> t -> bool

val terms : t -> Term.Set.t

val vars : t -> Term.Set.t

val inconsistent : t -> bool
(** Do all disjuncts entail false in the sense of [Heap.inconsistent]? *)

val subsumed : ?total:bool -> t -> t -> bool
(** Works similar to the unify functions but without renaming of vars 
    If the optional argument [~total=true] is set to [false] then relax the
    check on the spatial part so that it is included rather than equal to that
    of [b].*)

val parse :
    ?augment_deqs:bool
  -> (t, 'a) MParser.t

val of_string : string -> t

val star : ?augment_deqs:bool -> t -> t -> t
(** Star two formulas by distributing [*] through [+]. *)

val subst : Subst.t -> t -> t

val subst_existentials : t -> t
(** Like [Heap.subst_existentials] applied to all disjuncts. *)

val univ : Term.Set.t -> t -> t
(** univ(avoid, repl) Replace all existential variables with fresh universal variables. *)

val norm : t -> t
(** Replace all terms with their UF representatives in the respective heaps. *)

val equates : t -> Term.t -> Term.t -> bool

val disequates : t -> Term.t -> Term.t -> bool

val unify_partial :
     ?update_check:Unify.Unidirectional.update_check
  -> ((t * Pred.t) list * (Predsym.t * (Int.t * (Predsym.t list)))) list
  -> t Unify.Unidirectional.unifier
(** [unify_partial avoid_tags hs hs' cont init_state]
    Unify two heapsums (substitute vars and tags), such that every summand h of hs matches with one summand h' of hs',
    where h' can be matched by at most one h. h needs to be a subformula of h'.
    This is used for backlinking (matching LHS, hs is target, hs' is source).
    This requires the factor of summands to be exactly 1*)

val classical_unify :
     ?match_whole:bool
  -> ?update_check:Unify.Unidirectional.update_check
  -> t Unify.Unidirectional.unifier
(** [classical_unify ?match_whole avoid_tags hs hs' cont init_state]
    Unify two heapsums (substitute vars and tags), such that every summand h' of hs' matches with one summand h of hs,
    where h can be matched by at most one h'.
    The pure part of h needs to be a subformula of h' whilst the spatial part needs to be equal.
    This is used in various occasions, including splitting id summands, ... .
    If match_whole is false, return after the first summand has been matched and not every summand of hs' has to be matched.
    This requires the factor of summands to be exactly 1*)

val classical_biunify :
     ?update_check:Unify.Bidirectional.update_check
  -> t Unify.Bidirectional.unifier
(** [classical_biunify avoid_tags hs hs' cont init_state]
    Unify two heapsums (substitute vars and tags), such that every summand h' of hs' matches with one summand h of hs,
    where h can be matched by at most one h'.
    The pure part of h needs to be a subformula of h' whilst the spatial part needs to be equal.
    This is used for backlinking (matching RHS, hs' is target, hs is source).
    This requires the factor of summands to be exactly 1*)

val is_precise : (((t * Pred.t) list) * (Predsym.t * (Int.t * (Predsym.t list)))) list -> t -> bool
(** [is_precise defs f] calculates if every existential var of f 
    on a left side of a points to predicate is fixed. If f consists of multiple
    disjuncts or summands it is not considered precise. Predicates are considered
    precise if they are marked so in the definitions and if they use existential
    vars as arguments the predicates are only precise if they are marked so in the
    proof tree. A predicate loses its precise marking if the formula changed by
    a change other than just predicate unfolding.
    The function uses defs for predicate definitions.*)