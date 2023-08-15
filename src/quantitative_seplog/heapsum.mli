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

val has_untagged_preds : t -> bool

val inconsistent : t -> bool
(** Do all disjuncts entail false in the sense of [Heap.inconsistent]
    or are the tag constraints inconsistent? *)

val most_special_subsumption: ?total:bool -> Heap.t -> t -> t list
(** [most_special_subsumption h hs] Calculates for every summand of hs if h is subsumed by
    it and returns the list of the lists resulting from splitting the most special subsumptions from hs.
    Most special meaning the product with the least amount of multiplicants*)

val subsumed : ?total:bool -> t -> t -> bool
(** [subsumed a b]: is it the case that
      for any disjunct [a'] of [a] there is a disjunct [b'] of [b] such that
          [a'] is subsumed by [b']?
    If the optional argument [~total=true] is set to [false] then relax the
    check on the spatial part so that it is included rather than equal to that
    of [b].
    NB this includes matching the tags exactly. *)

val subsumed_upto_tags : ?total:bool -> t -> t -> bool
(** As above but ignoring tags.
    If the optional argument [~total=true] is set to [false] then relax the
    check on the spatial part so that it is included rather than equal to that
    of [b]. *)

val parse :
  ?allow_tags:bool
  -> ?augment_deqs:bool
  -> (t, 'a) MParser.t

val of_string : string -> t

val star : ?augment_deqs:bool -> t -> t -> t
(** Star two formulas by distributing [*] through [+]. *)

val subst : Subst.t -> t -> t

val subst_existentials : t -> t
(** Like [Heap.subst_existentials] applied to all disjuncts. *)

val subst_tags : Tagpairs.t -> t -> t
(** Like [Heap.subst_tags] applied to all disjuncts. *)

val univ : Term.Set.t -> t -> t
(** univ(avoid, repl) Replace all existential variables with fresh universal variables. *)

val norm : t -> t
(** Replace all terms with their UF representatives in the respective heaps. *)

val equates : t -> Term.t -> Term.t -> bool

val disequates : t -> Term.t -> Term.t -> bool