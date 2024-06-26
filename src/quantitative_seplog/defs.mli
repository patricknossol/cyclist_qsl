open Lib
open Generic

include BasicType

val empty : t

val add : Preddef.t -> t -> t

val to_list : t -> Preddef.t list

val of_list : Preddef.t list -> t

val mem : Predsym.t -> t -> bool

val is_defined : t -> Tpred.t -> bool

val is_undefined : t -> Tpred.t -> bool

val get_preddef : Predsym.t -> t -> Preddef.t

val get_def : Predsym.t -> t -> Indrule.t list

val get_def_forms : t -> (Predsym.t * Form.t) list

val fixpoint : (t -> t) -> t -> t

(*val relevant_defs : t -> Form.t -> t*)

val check_form_wf : t -> Form.t -> unit

val check_consistency : t -> unit

val rule_fold : ('a -> Indrule.t -> 'a) -> 'a -> t -> 'a

val rule_iter : (Indrule.t -> unit) -> t -> unit

val parse : (t, 'a) MParser.t

val of_channel : in_channel -> t

val of_string : string -> t

val unfold :
  Term.Set.t -> Tpred.t -> t -> Heapsum.t list
(** [unfold (vs, ts) p defs] returns a list containing the bodies of all the
    inductive rules for [p] in [defs] where, for each rule body:
      the formal parameters have been replaced by the arguments of [p];
      the remaining variables have been freshened, avoiding those in [vs]
*)
