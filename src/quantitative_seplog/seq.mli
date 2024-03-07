(** SL sequent, as a pair of SL formulas. *)
open Lib
open Generic

include BasicType with type t = Form.t * Form.t

val equal_upto_tags : t -> t -> bool
(** Like [equal] but ignoring LHS tags as well as RHS ones. *)

val dest :
  t -> (Ord_constraints.t * Heap.t) * (Ord_constraints.t * Heap.t)
(** If both LHS and RHS are symbolic heaps then return them else raise
    [Form.Not_symheap]. *)

val dest_sum :
  t -> (Ord_constraints.t * Heapsum.t) * (Ord_constraints.t * Heapsum.t)
(** If both LHS and RHS are symbolic heap sums then return them else raise
    [Form.Not_symheap_sum]. *)

val parse : ?null_is_emp:bool -> (t, 'a) MParser.t

val of_string : ?null_is_emp:bool -> string -> t

val vars : t -> Term.Set.t

val tags : t -> Tags.t
(** Tags occurring in this sequent on both the LHS and RHS *)

val tag_pairs : t -> Tagpairs.t
(** Tag pairs constituting the identity relation on the tags in the LHS. *)

val get_tracepairs : t -> t -> Tagpairs.t * Tagpairs.t
(** Get the tracepairs between two sequents *)

val subst_tags : Tagpairs.t -> t -> t
(** Substitute tags of the LHS. *)

val subst : Subst.t -> t -> t

val subsumed : t -> t -> bool
(** [subsumed (l,r) (l',r')] is true iff both [Form.subsumed l' l] and
    [Form.subsumed r r'] are true. *)

val norm : t -> t
(** Replace all terms with their UF representatives in the respective formulas.` *)

val split_sum : t -> t
(** Split summands with a number > 1 to multiple summands with a number = 1
    and rename ex. vars/tags in new summands*)

val partition_summands : t -> (int * int) list -> t * t
(**Split formulas into two formulas, one containing only summands at the indices given in the
    respective entries in the pair, the other containing the rest of the summands.
    The summands on the right side of the first returned sequence are ordered, so that they appear in
    the same order as the summands they match with on the left hand side.*)

val set_precise_preds : Preddef.t list -> t -> t
(** [set_precise_preds defs f] sets all appropiate predicates to be precise*)

val reduce_zeros : t -> t
(** [reduce_zeros f] sets 0 * ... to 0 and 0 + a to a*)

val rational_to_natural_nums : t -> t