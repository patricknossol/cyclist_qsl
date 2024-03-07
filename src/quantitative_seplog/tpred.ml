open Lib
open   Symbols

open Generic

open MParser

module TPred = Pair.Make (Int) (Pred)
include TPred

let subst theta (precise, pred) = (precise, Pred.subst theta pred)

let equal (_, p1) (_, p2) = Pred.equal p1 p2

let compare (_, p1) (_, p2) = Pred.compare p1 p2

let unify ?(update_check = Fun._true) (_, pred) (_, pred')
    cont init_state =
  Pred.unify ~update_check pred pred' cont init_state

let biunify ?(update_check = Fun._true) (_, pred)
    (_, pred') cont init_state =
  Pred.biunify ~update_check pred pred' cont init_state

let precise_tag (precise, _) = precise > 0

let predsym (_, tpred) = Pred.predsym tpred

let args (_, tpred) = Pred.args tpred

let arity (_, tpred) = Pred.arity tpred

let terms (_, tpred) = Pred.terms tpred

let vars tpred = Term.filter_vars (terms tpred)

let to_string (_, (pred, args)) =
  Predsym.to_string pred
  ^ bracket (Term.FList.to_string_sep symb_comma.sep args)

let parse st =
  ( Predsym.parse
  >>= (fun pred ->
        (return None)
        >>= fun opt_tag ->
        Tokens.parens (Tokens.comma_sep Term.parse)
        << spaces
        >>= fun arg_list ->
        return (0, (pred, arg_list)) )
  <?> "ind" )
    st

let norm eqs (precise, pred) = (precise, Pred.norm eqs pred)

let of_string = mk_of_string parse

let pp fmt (_, pred) =
  Format.fprintf fmt "@[%a%s%s%s%s@]" Predsym.pp (Pred.predsym pred)
    ("")
    symb_lp.str
    (Term.FList.to_string_sep symb_comma.sep (Pred.args pred))
    symb_rp.str
