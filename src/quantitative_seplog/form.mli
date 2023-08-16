(** SL formula, basically a list of sums over symbolic heaps, denoting their disjunction,
    along with a set of contraints on predicate ordinal labels (tags).
    NB no attempt to enforce variable or tag hygiene is made.  For example,
    if [f] and [g] both use an existential variable [x'] then [[f;g]] would
    mean the bound variable is shared. *)

open Lib
open Generic

include BasicType with type t = Ord_constraints.t * Heapsum.t list

val empty : t
(** The formula [emp]. NB this is not the same as [[]], which is equivalent to
    false. *)

exception Not_symheap
exception Not_symheap_sum

val is_symheap : t -> bool
(** Returns true iff the formula has a single disjunct only *)

val dest : t -> Ord_constraints.t * Heap.t
(** Return the single disjunct and single summand, if there is exactly one, else raise [Not_symheap]. *)

val dest_sum :
    t -> Ord_constraints.t * Heapsum.t
  (** If both formula is a sum of symbolic heaps then return them else raise 
      [Form.Not_symheap_sum]. *)

val equal_upto_tags : t -> t -> bool
(** Whilst [equal] demands syntactic equality including tags, this version
    ignores tag assignment. *)

val terms : t -> Term.Set.t

val vars : t -> Term.Set.t

val tags : t -> Tags.t
(** NB no attempt is made to ensure that tags are disjoint between disjuncts.
    This is not necessarily unsound. *)

val tag_pairs : t -> Tagpairs.t
(** The proviso on tags applies here too. *)

val complete_tags : Tags.t -> t -> t
(** [complete_tags ts f] returns the formula obtained from f by assigning
    all untagged predicates a fresh existential tag, avoiding those in [ts].
*)

val inconsistent : t -> bool
(** Do all disjuncts entail false in the sense of [Heap.inconsistent]
    or are the tag constraints inconsistent? *)

val subsumed : ?total:bool -> t -> t -> bool
(** [subsumed a b]: is it the case that
      i)  the constraints cs of [a] are subsumed by the constraints cs' of [b]
          in the sense that [Ord_constraints.subsumes cs' cs] returns [true]
      ii) for any disjunct [a'] of [a] there is a disjunct [b'] of [b] such that
          [a'] is subsumed by [b']?
    If the optional argument [~total=true] is set to [false] then relax the
    check on the spatial part so that it is included rather than equal to that
    of [b].
    NB this includes matching the tags exactly. *)

val subsumed_upto_constraints : ?total:bool -> t -> t -> bool
(** As above but does not check subsumption of constraints *)

val subsumed_upto_tags : ?total:bool -> t -> t -> bool
(** As above but ignoring tags.
    If the optional argument [~total=true] is set to [false] then relax the
    check on the spatial part so that it is included rather than equal to that
    of [b]. *)

val parse :
     ?null_is_emp:bool
  -> ?allow_tags:bool
  -> ?augment_deqs:bool
  -> (t, 'a) MParser.t

val of_string : ?null_is_emp:bool -> string -> t

val star : ?augment_deqs:bool -> t -> t -> t
(** Star two formulas by distributing [*] through [\/]. *)

val disj : t -> t -> t
(** Or two formulas (list-append). *)

val subst : Subst.t -> t -> t

val subst_existentials : t -> t
(** Like [Heap.subst_existentials] applied to all disjuncts. *)

val subst_tags : Tagpairs.t -> t -> t
(** Like [Heap.subst_tags] applied to all disjuncts. *)

val norm : t -> t
(** Replace all terms with their UF representatives in the respective heaps. *)

val with_constraints : t -> Ord_constraints.t -> t
(** [with_constraints f cs] returns the formula that results by replacing [f]'s
    tag constraints with [cs] *)

val add_constraints : t -> Ord_constraints.t -> t
(** [add_constraints f cs] returns the formula the results by adding [cs] to the
    constraints already in [f] *)

val with_heapsums : t -> Heapsum.t list -> t
(** [with_heapsums hs cs] returns the formula that results by replacing [f]'s
    disjunction of heapsums with [hs] *)

val get_tracepairs : t -> t -> Tagpairs.t * Tagpairs.t
(** [get_tracepairs f f'] will return the valid and progressing trace pairs
    (t, t') specified by the constraints of [f'] such that [t] occurs in [f]
*)

val is_domain_exact : ?covered:Predsym.t list -> (Predsym.t * t) list -> t -> bool
(** [is_domain_exact covered defs f] calculates if f is domain_exact considering
    that the predicate symbols in covered have already been analyzed*)

val mk_heap : Heap.t -> t

val mk_heapsums : Heapsum.t list -> t