open Lib
open Symbols
open Qsl_symbols

open Generic

open MParser

include Flist.Make (Heap)

exception Not_symheap

let empty = []

let is_empty hs = hs = empty || hs = [Heap.empty]

let dest : t -> Heap.t = function
  | [s] -> s
  | _ -> raise Not_symheap

let pp fmt hs =
  let pp_plus fmt () = Format.fprintf fmt " %s@ " symb_plus.str in
  Format.fprintf fmt "@[%a@]" (Blist.pp pp_plus Heap.pp) hs

let to_string hs =
  Blist.to_string symb_plus.sep Heap.to_string hs

let terms hs = Term.Set.union_of_list (Blist.map Heap.terms hs)

let vars hs = Term.filter_vars (terms hs)

let tags hs =
  Tags.union_of_list (Blist.map Heap.tags hs)

let tag_pairs hs = Tagpairs.mk (tags hs)

let inconsistent hs =
  Blist.for_all Heap.inconsistent hs

let complete_tags avoid hs =
  let hs = 
    Blist.rev
      (Blist.foldr
        (fun h hs' ->
          let h' =
            if Heap.has_untagged_preds h then
              let avoid' =
                Blist.foldl
                  (fun ts h -> Tags.union ts (Heap.tags h))
                  avoid hs'
              in
              Heap.complete_tags avoid' h
            else h
          in
          h' :: hs' )
        (Blist.rev hs) [])
    in
    hs
  
let has_untagged_preds hs =
  let res =
    (Blist.foldr
      (fun h b ->
        if Heap.has_untagged_preds h then
          true
        else
          (b || false)
      )
      hs false)
  in
  res

let most_special_subsumption ?(upto_tags = false) ?(total = true) h hs' =
  (*TODO print_endline "HII TEST SUBSUMED";*) 
  Blist.foldr (
    fun h' list ->
      let h_is_subsumed =
        if upto_tags then Heap.subsumed_upto_tags ~total h h'
        else Heap.subsumed ~total h h' in
      if h_is_subsumed then
        let h'_minus_h = (Heap.sub_num h' h.num) in
        let hs'_wo_h' = Blist.del_first (fun h2 -> h2 = h') hs' in
        if h'_minus_h.num > 0. then (h'_minus_h :: hs'_wo_h') :: list else hs'_wo_h' :: list
      else list
  ) hs' []

let rec subsumed ?(total = true) hs hs' =
  match hs with
    | [] -> true
    | h::hs -> (
      let hslist = most_special_subsumption ~total h hs' in
      Blist.exists (fun hs2 -> subsumed ~total hs hs2) hslist
    )

let subsumed_upto_tags ?(total = true) hs hs' =
  match hs with
    | [] -> true
    | h::hs -> (
      let hslist = most_special_subsumption ~upto_tags:true ~total h hs' in
      Blist.exists (fun hs2 -> subsumed ~total hs hs2) hslist
    )

let equal_upto_tags hs hs' =
  Blist.for_all2 Heap.equal_upto_tags hs hs'

let parse ?(allow_tags = true) ?(augment_deqs = true) st =
  (sep_by (Heap.parse ~allow_tags ~augment_deqs) (parse_symb symb_plus)
  <?> "heapsum"
  >>= fun hs ->
  return
    hs)
    st

let of_string s =
  handle_reply (MParser.parse_string (parse ~allow_tags:true ~augment_deqs:true) s ())

let star ?(augment_deqs = true) f g = (*TODO check if okay to do for debugging*)
  let hs =
    Blist.map
      (fun (f', g') -> Heap.star ~augment_deqs f' g')
      (Blist.cartesian_product f g)
  in hs

let subst theta hs = Blist.map (fun h -> Heap.subst theta h) hs

let subst_existentials hs = Blist.map Heap.subst_existentials hs

let subst_tags tagpairs hs =
  Blist.map (Heap.subst_tags tagpairs) hs

let univ s hs =
  Blist.map (fun h -> Heap.univ s h) hs

let norm hs = Blist.map Heap.norm hs

let equates hs a b =
  Blist.for_all (fun h -> Heap.equates h a b) hs

let disequates hs a b =
    Blist.for_all (fun h -> Heap.disequates h a b) hs

let rec unify_partial_rec ?(tagpairs = true) ?(update_check = Fun._true) hs hs' cont init_state =
  match hs' with
    | [] -> [(init_state, hs')]
    | h'::hs' -> 
      let subs = Blist.foldr
        (fun h list ->
          let state = Heap.unify_partial ~tagpairs ~update_check h h' cont init_state in
          if Option.is_some state then
            let dif = Heap.sub_num h h'.Heap.num in
            let hs_wo_dif = Blist.del_first (fun h2 -> h2 = h) hs in
            if dif.num > 0. then (Option.get state, (dif :: hs_wo_dif)) :: list else (Option.get state, hs_wo_dif) :: list
          else list
        ) hs [] in
      Blist.flatten (Blist.map (fun (state, sub) -> unify_partial_rec ~tagpairs ~update_check sub hs' cont state) subs)

let unify_partial ?(tagpairs = true) ?(update_check = Fun._true) hs hs' cont init_state =
  let results = unify_partial_rec ~tagpairs ~update_check hs hs' cont init_state in
  match results with
    | [] -> None
    | (state, _) :: results -> Some(state)

let rec biunify_partial_rec ?(tagpairs = true) ?(update_check = Fun._true) hs hs' cont init_state =
  match hs' with
    | [] -> [(init_state, hs')]
    | h'::hs' -> 
      let subs = Blist.foldr
        (fun h list ->
          let state = Heap.biunify_partial ~tagpairs ~update_check h h' cont init_state in
          if Option.is_some state then
            let dif = Heap.sub_num h h'.Heap.num in
            let hs_wo_dif = Blist.del_first (fun h2 -> h2 = h) hs in
            if dif.num > 0. then (Option.get state, (dif :: hs_wo_dif)) :: list else (Option.get state, hs_wo_dif) :: list
          else list
        ) hs [] in
      Blist.flatten (Blist.map (fun (state, sub) -> biunify_partial_rec ~tagpairs ~update_check sub hs' cont state) subs)

let biunify_partial ?(tagpairs = true) ?(update_check = Fun._true) hs hs' cont init_state =
  let results = biunify_partial_rec ~tagpairs ~update_check hs hs' cont init_state in
  match results with
    | [] -> None
    | (state, _) :: results -> Some(state)

let rec classical_unify_rec ?(tagpairs = true) ?(update_check = Fun._true) hs hs' cont init_state =
  match hs' with
    | [] -> [(init_state, hs')]
    | h'::hs' -> 
      let subs = Blist.foldr
        (fun h list ->
          let state = Heap.classical_unify ~tagpairs ~update_check h h' cont init_state in
          if Option.is_some state then
            let dif = Heap.sub_num h h'.Heap.num in
            let hs_wo_dif = Blist.del_first (fun h2 -> h2 = h) hs in
            if dif.num > 0. then (Option.get state, (dif :: hs_wo_dif)) :: list else (Option.get state, hs_wo_dif) :: list
          else list
        ) hs [] in
      Blist.flatten (Blist.map (fun (state, sub) -> classical_unify_rec ~tagpairs ~update_check sub hs' cont state) subs)

let classical_unify ?(tagpairs = true) ?(update_check = Fun._true) hs hs' cont init_state =  
  let results = classical_unify_rec ~tagpairs ~update_check hs hs' cont init_state in
  match results with
    | [] -> None
    | (state, _) :: results -> Some(state)
  
let rec classical_biunify_rec ?(tagpairs = true) ?(update_check = Fun._true) hs hs' cont init_state =
  match hs' with
    | [] -> [(init_state, hs')]
    | h'::hs' -> 
      let subs = Blist.foldr
        (fun h list ->
          let state = Heap.classical_biunify ~tagpairs ~update_check h h' cont init_state in
          if Option.is_some state then
            let dif = Heap.sub_num h h'.Heap.num in
            let hs_wo_dif = Blist.del_first (fun h2 -> h2 = h) hs in
            if dif.num > 0. then (Option.get state, (dif :: hs_wo_dif)) :: list else (Option.get state, hs_wo_dif) :: list
          else list
        ) hs [] in
      Blist.flatten (Blist.map (fun (state, sub) -> classical_biunify_rec ~tagpairs ~update_check sub hs' cont state) subs)

let classical_biunify ?(tagpairs = true) ?(update_check = Fun._true) hs hs' cont init_state =
  let results = classical_biunify_rec ~tagpairs ~update_check hs hs' cont init_state in
  match results with
    | [] -> None
    | (state, _) :: results -> Some(state)