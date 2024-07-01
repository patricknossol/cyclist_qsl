open Lib
open   Symbols

open Generic

open MParser

include Multiset.Make (Tpred)

let subst theta elts = map (Tpred.subst theta) elts

let terms inds =
  Term.Set.union_of_list (Blist.map Tpred.terms (elements inds))

let vars inds = Term.filter_vars (terms inds)

let idents inds =
  map_to Predsym.MSet.add Predsym.MSet.empty
    (fun (_, ((id, _), _)) -> id)
    inds

let to_string_list v = Blist.map Tpred.to_string (elements v)

let to_string v = Blist.to_string symb_star.sep Tpred.to_string (elements v)

let equal inds inds' =
  Pred.MSet.equal (map_to Pred.MSet.add Pred.MSet.empty (fun (_, (ind, _)) -> ind) inds) (map_to Pred.MSet.add Pred.MSet.empty (fun (_, (ind, _)) -> ind) inds')

let unify ?(allow_conform = false) ?(total = true) ?(update_check = Fun._true) inds
    inds' cont init_state =
  mk_unifier total true
    (Tpred.unify ~allow_conform ~update_check)
    inds inds' cont init_state

let biunify ?(total = true) ?(update_check = Fun._true) inds
    inds' cont init_state =
  mk_unifier total true
    (Tpred.biunify ~update_check)
    inds inds' cont init_state

let rec subsumed ?(total = true) eqs inds inds' =
  if is_empty inds then (not total) || is_empty inds'
  else
    let ind = choose inds in
    let inds = remove ind inds in
    let ind = Tpred.norm eqs ind in
    match
      find_opt (fun ind' -> Tpred.equal ind (Tpred.norm eqs ind')) inds'
    with
    | None -> false
    | Some ind' -> subsumed ~total eqs inds (remove ind' inds')

let norm eqs inds = map (Tpred.norm eqs) inds
