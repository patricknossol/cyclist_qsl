open Lib
open Symbols
open Qsl_symbols
open MParser
include Pair.Make (Flist.Make (Indrule)) (Pair.Make (Predsym) (Pair.Make (Int) (Flist.Make (Predsym))))

let dest d = d

let predsym (_, (p, _)) = p

let is_precise (_, (_, (p, _))) = p > 0

let is_conform_with (_, (_, (_, conform_list))) pred =
  Blist.mem pred conform_list

let rules = fst

let pp fmt (rules, (predsym, _)) =
  Format.fprintf fmt "@[<v 2>%a%s@.%a@.%s@]" Predsym.pp predsym symb_lb.sep
    (Blist.pp
       (fun fmt () -> Format.fprintf fmt "%s@." symb_ind_sep.sep)
       Indrule.pp)
    rules symb_rb.str

let to_string (rules, (predsym, _)) =
  Predsym.to_string predsym
  ^ symb_lb.sep ^ "\n"
  ^ Blist.to_string (symb_ind_sep.sep ^ "\n") Indrule.to_string rules
  ^ "\n" ^ symb_rb.str

let mk ((rules, (predsym, _)) as def) =
  assert (not (Blist.is_empty rules)) ;
  let a = Indrule.arity (Blist.hd rules) in
  assert (Blist.for_all (fun r -> Int.equal a (Indrule.arity r)) rules) ;
  assert (
    Blist.for_all
      (fun r -> Predsym.equal predsym (Indrule.predsym r))
      rules ) ;
  def

let rules_heapsums indrules =
  Blist.map (fun rule ->
    Indrule.body rule
  ) indrules

let parse st =
  ( spaces >> Predsym.parse
  >>= (fun name ->
        spaces >> option (parse_symb symb_pred_precise) >>=
        (fun precise_opt ->
          spaces >> option (parse_symb symb_pred_conform) >>=
          (fun conform_opt -> 
              if Option.is_some conform_opt then
                spaces >> sep_by1 Predsym.parse (spaces) >>=
                (fun conform_list ->
                  Tokens.braces (sep_by1 Indrule.parse (parse_symb symb_ind_sep))
                  << spaces
                  >>= fun cases -> return (mk (cases, (name, ((if Option.is_none precise_opt then 0 else 1), conform_list))))
                )
              else
                Tokens.braces (sep_by1 Indrule.parse (parse_symb symb_ind_sep))
                << spaces
                >>= fun cases -> return (mk (cases, (name, ((if Option.is_none precise_opt then 0 else 1), []))))
          )
        )
      )
  <?> "preddef" )
    st