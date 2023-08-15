open Lib
open   Symbols

open Generic

open MParser

include Pair.Make (Heapsum) (Pred)

let vars (f, (_, vs)) =
  Term.Set.union (Term.Set.of_list vs) (Heapsum.vars f)

let mk f ((_, args) as hd) =
  let v_args = Term.Set.of_list args in
  let v_h = Heapsum.terms f in
  let uv_h, ev_h = Term.Set.partition Term.is_free_var v_h in
  assert (Blist.for_all Term.is_free_var args) ;
  assert (Int.equal (Term.Set.cardinal v_args) (Blist.length args)) ;
  assert (Term.Set.subset uv_h v_args) ;
  assert (
    Term.Set.for_all
      (fun trm -> Term.is_nil trm || Term.is_exist_var trm)
      ev_h ) ;
  (f, hd)

let dest c = c

let predsym (_, pred) = Pred.predsym pred

let arity (_, pred) = Pred.arity pred

let formals (_, pred) = Pred.args pred

let body (h, _) = h

let subst theta (f, (ident, args)) =
  let f = Heapsum.subst theta f in
  let args = Term.FList.subst theta args in
  let v_args = Term.Set.of_list args in
  let v_h = Heapsum.terms f in
  let uv_h, ev_h = Term.Set.partition Term.is_free_var v_h in
  assert (Blist.for_all Term.is_free_var args) ;
  assert (Int.equal (Term.Set.cardinal v_args) (Blist.length args)) ;
  assert (Term.Set.subset uv_h v_args) ;
  assert (
    Term.Set.for_all
      (fun trm -> Term.is_nil trm || Term.is_exist_var trm)
      ev_h ) ;
  (f, (ident, args))

let freshen varset case =
  let casevars = vars case in
  let theta = Subst.avoid varset casevars in
  subst theta case

let pp fmt (f, (ident, vs)) =
  Format.fprintf fmt "@[%a%s%a%s%s%s@]" Heapsum.pp f symb_ind_implies.sep
    Predsym.pp ident symb_lp.str
    (Blist.to_string "," Term.to_string vs)
    symb_rp.str

let to_string c = mk_to_string pp c

let parse st =
  ( Heapsum.parse ~allow_tags:false
  >>= (fun h ->
        parse_symb symb_ind_implies
        >> Pred.parse << spaces
        >>= fun head -> return (mk h head) )
  <?> "case" )
    st

let unfold ?(gen_tags = true) (vars, tags) (tag, (ident, args)) case =
  let f, (ident', formals) = dest (freshen vars case) in
  assert (Predsym.equal ident ident') ;
  assert (Blist.length args == Blist.length formals) ;
  assert (Tags.is_empty (Heapsum.tags f)) ;
  let f = if gen_tags then Heapsum.complete_tags tags f else f in
  let theta = Term.Map.of_list (Blist.combine formals args) in
  Heapsum.subst theta f