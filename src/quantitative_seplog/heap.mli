(** Symbolic heaps. *)

open Lib
open Generic

type abstract1

type symheap = private
  { eqs: Uf.t
  ; deqs: Deqs.t
  ; ptos: Ptos.t
  ; inds: Tpreds.t
  ; num: Num.t
  ; mutable _terms: abstract1
  ; mutable _vars: abstract1 }

include BasicType with type t = symheap

val empty : t
(*emp. Not the same as [] = 0]*)

(** Accessor functions. *)

val vars : t -> Term.Set.t

val terms : t -> Term.Set.t

val equates : t -> Term.t -> Term.t -> bool
(** Does a symbolic heap entail the equality of two terms? *)

val disequates : t -> Term.t -> Term.t -> bool
(** Does a symbolic heap entail the disequality of two terms? *)

val find_lval : Term.t -> t -> Pto.t option
(** Find pto whose address is provably equal to given term. *)

val idents : t -> Predsym.MSet.t
(** Get multiset of predicate identifiers. *)

val inconsistent : t -> bool
(** Trivially false if heap contains t!=t for any term t, or if x=y * x!=y
    is provable for any x,y.
    NB only equalities and disequalities are used for this check.
*)

val subsumed : ?total:bool -> ?with_num:bool -> t -> t -> bool
(** [subsumed h h'] is true iff [h] can be rewritten using the equalities
    in [h'] such that its spatial part becomes equal to that of [h']
    and the pure part becomes a subset of that of [h'].
    If the optional argument [~total=true] is set to [false] then check whether
    both pure and spatial parts are subsets of those of [h'] modulo the equalities
    of [h']. *)

val equal : t -> t -> bool
(** Checks whether two symbolic heaps are equal. *)

val equal_upto_num : t -> t -> bool

val is_empty : t -> bool
(** [is_empty h] tests whether [h] is equal to the empty heap. *)

(** Constructors. *)

val parse : ?augment_deqs:bool -> (t, 'a) MParser.t

val of_string : ?augment_deqs:bool -> string -> t

val mk_pto : Pto.t -> t

val mk_eq : Tpair.t -> t

val mk_deq : Tpair.t -> t

val mk_ind : Tpred.t -> t

val mk_num : int * int -> t

val mk : Uf.t -> Deqs.t -> Ptos.t -> Tpreds.t -> Num.t -> t

val dest : t -> Uf.t * Deqs.t * Ptos.t * Tpreds.t * Num.t

(** Functions [with_*] accept a heap [h] and a heap component [c] and
    return the heap that results by replacing [h]'s appropriate component
    with [c]. *)

val with_eqs : t -> Uf.t -> t

val with_deqs : t -> Deqs.t -> t

val with_ptos : t -> Ptos.t -> t

val with_inds : t -> Tpreds.t -> t

val with_num : t -> Num.t -> t

val del_deq : t -> Tpair.t -> t

val del_pto : t -> Pto.t -> t

val del_ind : t -> Tpred.t -> t

val del_num : t -> float -> t

val add_eq : t -> Tpair.t -> t

val add_deq : t -> Tpair.t -> t

val add_pto : t -> Pto.t -> t

val add_ind : t -> Tpred.t -> t

val explode_deqs : t -> t

val star : ?augment_deqs:bool -> t -> t -> t

val fixpoint : (t -> t) -> t -> t

val subst : Subst.t -> t -> t

val univ : Term.Set.t -> t -> t
(** univ(avoid, repl) Replace all existential variables with fresh universal variables. *)

val subst_existentials : t -> t
(** For all equalities x'=t, remove the equality and do the substitution [t/x'] *)

val copy_fresh_heap : Subst.var_container -> t -> t

val unify_partial :
     ?update_check:Unify.Unidirectional.update_check
  -> ?with_num:bool
  -> t Unify.Unidirectional.unifier
(** Unify two heaps such that the first becomes a subformula of the second. *)

val classical_unify :
    ?allow_conform:bool
  -> ?inverse:bool
  -> ?update_check:Unify.Unidirectional.update_check
  -> ?with_num:bool
  -> t Unify.Unidirectional.unifier
(** Unify two heaps, by using [unify_partial] for the pure (classical) part whilst
    using [unify] for the spatial part.
- If the optional argument [~inverse=false] is set to [true] then compute the
  required substitution for the *second* argument as opposed to the first. *)

val classical_biunify :
     ?update_check:Unify.Bidirectional.update_check
  -> ?with_num:bool
  -> t Unify.Bidirectional.unifier

val norm : t -> t
(** Replace all terms with their UF representative (the UF in the heap). *)

val all_subheaps : t -> t list
(** [all_subheaps h] returns a list of all the subheaps of [h]. These are
    constructed by taking:
      - all the subsets of the disequalities of [h];
      - all the subsets of the points-tos of [h];
      - all the subsets of the predicates of [h];
      - the equivalence classes of each subset of variables in the equalities of
        [h] that also respect the equalities of [h] are constructed - this is
        done by using [Uf.remove] to remove subsets of variables from
        [h.eqs];
    and forming all possible combinations *)

val calc_spatial_frame : t -> t -> t * t
(* h' - h *)