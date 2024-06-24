open Lib
open   Symbols

open Generic

open MParser

module TPred = Pair.Make (Int) (Pair.Make (Pred) (Flist.Make (Predsym)))
include TPred

let subst theta (precise, (pred, conforms)) = (precise, (Pred.subst theta pred, conforms))

let equal (_, (p1, _)) (_, (p2, _)) = Pred.equal p1 p2

let compare (_, (p1, _)) (_, (p2, _)) = Pred.compare p1 p2

let unify ?(allow_conform = false) ?(update_check = Fun._true) (_, (pred, conform_list)) (_, (pred', conform_list'))
    cont init_state =
  Pred.unify ~allow_conform ~conform_list:conform_list ~conform_list':conform_list' ~update_check pred pred' cont init_state

let biunify ?(update_check = Fun._true) (_, (pred, _))
    (_, (pred', _)) cont init_state =
  Pred.biunify ~update_check pred pred' cont init_state

let precise_tag (precise, _) = precise > 0

let predsym (_, (tpred, _)) = Pred.predsym tpred

let args (_, (tpred, _)) = Pred.args tpred

let conform_list (_, (_, l)) = l

let arity (_, (tpred, _)) = Pred.arity tpred

let terms (_, (tpred, _)) = Pred.terms tpred

let vars tpred = Term.filter_vars (terms tpred)

let to_string (_, ((pred, args), _)) =
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
        return (0, ((pred, arg_list), [])) )
  <?> "ind" )
    st

let norm eqs (precise, (pred, conforms)) = (precise, (Pred.norm eqs pred, conforms))

let of_string = mk_of_string parse

let pp fmt (_, (pred, _)) =
  Format.fprintf fmt "@[%a%s%s%s%s@]" Predsym.pp (Pred.predsym pred)
    ("")
    symb_lp.str
    (Term.FList.to_string_sep symb_comma.sep (Pred.args pred))
    symb_rp.str
