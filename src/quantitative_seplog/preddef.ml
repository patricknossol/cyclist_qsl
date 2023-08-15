open Lib
open Symbols
open MParser
include Pair.Make (Flist.Make (Indrule)) (Predsym)

let dest d = d

let predsym = snd

let rules = fst

let pp fmt (rules, predsym) =
  Format.fprintf fmt "@[<v 2>%a%s@.%a@.%s@]" Predsym.pp predsym symb_lb.sep
    (Blist.pp
       (fun fmt () -> Format.fprintf fmt "%s@." symb_ind_sep.sep)
       Indrule.pp)
    rules symb_rb.str

let to_string (rules, predsym) =
  Predsym.to_string predsym
  ^ symb_lb.sep ^ "\n"
  ^ Blist.to_string (symb_ind_sep.sep ^ "\n") Indrule.to_string rules
  ^ "\n" ^ symb_rb.str

let mk ((rules, predsym) as def) =
  assert (not (Blist.is_empty rules)) ;
  let a = Indrule.arity (Blist.hd rules) in
  assert (Blist.for_all (fun r -> Int.equal a (Indrule.arity r)) rules) ;
  assert (
    Blist.for_all
      (fun r -> Predsym.equal predsym (Indrule.predsym r))
      rules ) ;
  def

let parse st =
  ( spaces >> Predsym.parse
  >>= (fun name ->
        Tokens.braces (sep_by1 Indrule.parse (parse_symb symb_ind_sep))
        << spaces
        >>= fun cases -> return (mk (cases, name)) )
  <?> "preddef" )
    st