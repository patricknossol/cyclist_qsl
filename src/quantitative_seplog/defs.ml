open Lib
open   Symbols

open Generic

open MParser

module SH = Heap

module Defs = struct
  include Flist.Make (Preddef)

  let mem ident defs =
    Blist.exists
      (fun def -> Predsym.equal ident (Preddef.predsym def))
      defs

  let empty = []

  let to_list d = d

  let add def defs =
    assert (not (mem (Preddef.predsym def) defs)) ;
    def :: defs

  let of_list defs = Blist.foldl (fun d p -> add p d) empty defs

  let to_string defs =
    Blist.to_string (symb_semicolon.sep ^ "\n\n") Preddef.to_string defs

  let pp fmt d = Format.fprintf fmt "%s" (to_string d)

  let is_defined defs (_, ((ident, _), _)) = mem ident defs

  let is_undefined defs pred = not (is_defined defs pred)

  let get_preddef ident defs =
    Blist.find (fun def -> Predsym.equal ident (Preddef.predsym def)) defs

  let get_def ident defs =
    Preddef.rules
      (Blist.find
         (fun def -> Predsym.equal ident (Preddef.predsym def))
         defs)

  let get_def_forms defs =
    Blist.foldl (fun list def -> 
      list @ Blist.map (fun rule -> 
        let form = Indrule.body rule in
        (Indrule.predsym rule, Form.mk_heapsums [form])
      ) (Preddef.rules def)
    ) [] defs

  let unfold vars ((_, ((ident, _), _)) as pred) defs =
    Blist.map
      (Indrule.unfold vars pred)
      (get_def ident defs)

  let rule_fold f v defs =
    let f' v' def = Blist.foldl f v' (Preddef.rules def) in
    Blist.foldl f' v defs

  let rule_iter f defs =
    let f' def = Blist.iter f (Preddef.rules def) in
    Blist.iter f' defs

  (*let relevant_defs all_defs (_, hs) =
    let ident_set ids = Predsym.Set.of_list (Predsym.MSet.to_list ids) in
    let iterate preds =
      let add_preds pred preds =
        let rules = get_def pred all_defs in
        let add_preds_from_rule preds rule =
          let body, _ = Indrule.dest rule in
          let new_preds = ident_set (Heapsum.idents body) in
          Predsym.Set.union preds new_preds
        in
        Blist.foldl add_preds_from_rule preds rules
      in
      Predsym.Set.fold add_preds preds preds
    in
    let init_ids =
      let ident_mset =
        Blist.fold_right
          (fun h -> Predsym.MSet.union (Heapsum.idents h))
          hs Predsym.MSet.empty
      in
      ident_set ident_mset
    in
    let relevant_preds = Predsym.Set.fixpoint iterate init_ids in
    Predsym.Set.fold
      (fun pred defs -> add (Preddef.mk (get_def pred all_defs, pred)) defs)
      relevant_preds empty*)

  let check_form_wf defs (_, (_, f)) =
    let check_pred p =
      let predsym = Tpred.predsym p in
      let pname = Predsym.to_string predsym in
      if not (mem predsym defs) then
        invalid_arg ("Cannot find definition for predicate " ^ pname)
      else
        let def = get_def predsym defs in
        if not (Blist.is_empty def) then
          let expected = Indrule.arity (Blist.hd def) in
          let provided = Tpred.arity p in
          if not (Int.equal expected provided) then
            invalid_arg
              ( pname ^ " given " ^ Int.to_string provided
              ^ " arguments when its definition expects "
              ^ Int.to_string expected ^ "!" )
    in
    Blist.iter
      (fun hs ->
        Blist.iter (fun h ->
        let _, _, _, inds, _ = Heap.dest h in
        Tpreds.iter check_pred inds ) hs)
      f

  let check_consistency defs =
    rule_iter
      (fun rl ->
        try check_form_wf defs (Tags.anonymous, (Ord_constraints.empty, [Indrule.body rl]))
        with Invalid_argument s ->
          failwith
            ( "Error in definition of "
            ^ Predsym.to_string (Indrule.predsym rl)
            ^ ": " ^ s ) )
      defs

  let parse st =
    ( sep_by1 Preddef.parse (parse_symb symb_semicolon)
    >>= (fun preddefs ->
          eof
          >>$
          let defs =
            Blist.rev
              (Blist.fold_left
                 (fun defs d ->
                   let () =
                     debug (fun _ ->
                         "Parsing definition of: "
                         ^ Predsym.to_string (Preddef.predsym d) )
                   in
                   add d defs )
                 empty preddefs)
          in
          let () = check_consistency defs in
          defs )
    <?> "defs" )
      st

  let of_string s = handle_reply (MParser.parse_string parse s ())

  let of_channel c = handle_reply (MParser.parse_channel parse c ())

end

include Defs
include Fixpoint.Make (Defs)
