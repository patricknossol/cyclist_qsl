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
    (Blist.foldl
      (fun b h ->
        if Heap.has_untagged_preds h then
          true
        else
          (b || false)
      )
      false hs)
  in
  res

let rec subsumed_rec ?(total = true) ?(upto_tags = false) hs hs' =
  match hs with
    | [] -> true
    | h::hs ->
      let res = Blist.foldl
        (fun res h' ->
          if res then res else
          let res = 
            if upto_tags then Heap.subsumed_upto_tags ~total ~with_num:false h h'
            else Heap.subsumed ~total ~with_num:false h h' in
          if res then
            let dif = h.Heap.num -. h'.Heap.num in
            let (hs_upd, hs'_upd) =
              if dif = 0. then
                (hs, Blist.del_first (fun h2 -> h2 = h') hs')
              else if dif > 0. then
                (Heap.with_num h dif :: hs, Blist.del_first (fun h2 -> h2 = h') hs')
              else 
                (hs, Blist.map (fun h2 -> if h2 = h' then Heap.with_num h' dif else h2) hs')
            in
            subsumed_rec ~total ~upto_tags hs_upd hs'_upd
          else false
        ) false hs' in
      res

let subsumed ?(total = true) ?(upto_tags = false) hs hs' =
  let time = if !Stats.do_statistics then Stats.now() else 0. in
  let res = subsumed_rec ~total ~upto_tags hs hs' in
  (if !Stats.do_statistics then
    Test_stats.unify_calls := !Test_stats.unify_calls + 1;
    Test_stats.unify_time := !Test_stats.unify_time +. (Stats.time_since time););
  res

let subsumed_upto_tags ?(total = true) hs hs' =
  subsumed ~total ~upto_tags:true hs hs'

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

let cartesian_product_order xs ys =
  Blist.foldl (fun acc x -> Blist.foldl (fun acc' y -> acc'@ [(x, y)] ) acc ys) [] xs

let star ?(augment_deqs = true) f g =
  let hs =
    Blist.map
      (fun (f', g') -> Heap.star ~augment_deqs f' g')
      (cartesian_product_order f g)
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

let rec unify_partial_rec ?(tagpairs = true) ?(update_check = Fun._true) avoid_vars avoid_tags hs hs' cont init_state =
  match hs with
  | [] -> Some(init_state)
  | hs ->
  match hs' with
    | [] -> None
    | (h', index')::hs' ->
      let state = Blist.foldl
        (fun res (h, index) ->
          if Option.is_some res then res else
          let state = Heap.unify_partial ~tagpairs ~update_check ~with_num:false h h' Unification.trivial_continuation init_state in
          if Option.is_some state then
            let (v, t, mapping) = Option.get state in
            let mapping = mapping @ [(index, index')] in
            let dif = h.Heap.num -. h'.Heap.num in
            let (hs_upd, hs'_upd, avoid_vars, avoid_tags) =
              if dif = 0. then
                (Blist.del_first (fun (_, i) -> i = index) hs, hs', avoid_vars, avoid_tags)
              else if dif > 0. then
                let h_upd = Heap.copy_fresh_heap (avoid_vars, avoid_tags) (Heap.with_num h dif) in
                (Blist.map (fun (h2, i) -> if i = index then (h_upd, i) else (h2, i)) hs,
                hs',
                Term.Set.union avoid_vars (Heap.vars h_upd),
                Tags.union avoid_tags (Heap.tags h_upd))
              else 
                let h'_upd = Heap.copy_fresh_heap (avoid_vars, avoid_tags) (Heap.with_num h' dif) in
                (Blist.del_first (fun (h2, i) -> i = index) hs,
                (h'_upd, index') :: hs',
                Term.Set.union avoid_vars (Heap.vars h'_upd),
                Tags.union avoid_tags (Heap.tags h'_upd))
            in
            let state = unify_partial_rec ~tagpairs ~update_check avoid_vars avoid_tags hs_upd hs'_upd cont (v, t, mapping) in
            if Option.is_some state then state else None
          else None
        ) None hs in
      state

let unify_partial ?(tagpairs = true) ?(update_check = Fun._true) constraint_tags hs hs' cont init_state =
  let time = if !Stats.do_statistics then Stats.now() else 0. in
  let avoid_vars = (Term.Set.union (vars hs) (vars hs')) in
  let avoid_tags = (Tags.union (Tags.union (tags hs) (tags hs')) constraint_tags) in
  let hs, hs' = Pair.map (fun hs -> 
    let _, res = Blist.foldl (fun (index, res) h -> 
      (index + 1, res @ [(h, index)])
    ) (0, []) hs in
    res
  ) (hs, hs') in
  let res = unify_partial_rec ~tagpairs ~update_check
    avoid_vars avoid_tags
    hs hs' cont init_state
  in
  (if !Stats.do_statistics then
    Test_stats.unify_calls := !Test_stats.unify_calls + 1;
    Test_stats.unify_time := !Test_stats.unify_time +. (Stats.time_since time););
  match res with
    | None -> None
    | Some(res) -> cont res

let rec classical_unify_rec ?(match_whole = true) ?(tagpairs = true) ?(update_check = Fun._true) avoid_vars avoid_tags hs hs' cont init_state =
  (*hs' = ls, hs = rs*)
  match hs' with
    | [] -> Some(init_state)
    | (h', index')::hs' ->
      let state = Blist.foldl
        (fun res (h, index) ->
          if Option.is_some res then res else
          let state = Heap.classical_unify ~tagpairs ~update_check ~with_num:false h h' Unification.trivial_continuation init_state in
          if Option.is_some state then
            let (v, t, mapping) = Option.get state in
            let mapping = mapping @ [(index, index')] in
            if not match_whole then
              Some(v, t, mapping)
            else
              let dif = h.Heap.num -. h'.Heap.num in
              let (hs_upd, hs'_upd, avoid_vars, avoid_tags) =
                if dif = 0. then
                  (Blist.del_first (fun (_, i) -> i = index) hs, hs', avoid_vars, avoid_tags)
                else if dif > 0. then
                  let h_upd = Heap.copy_fresh_heap (avoid_vars, avoid_tags) (Heap.with_num h dif) in
                  (Blist.map (fun (h2, i) -> if i = index then (h_upd, i) else (h2, i)) hs,
                  hs',
                  Term.Set.union avoid_vars (Heap.vars h_upd),
                  Tags.union avoid_tags (Heap.tags h_upd))
                else 
                  let h'_upd = Heap.copy_fresh_heap (avoid_vars, avoid_tags) (Heap.with_num h' dif) in
                  (Blist.del_first (fun (h2, i) -> i = index) hs,
                  (h'_upd, index') :: hs',
                  Term.Set.union avoid_vars (Heap.vars h'_upd),
                  Tags.union avoid_tags (Heap.tags h'_upd))
              in
              let state = classical_unify_rec ~tagpairs ~update_check avoid_vars avoid_tags hs_upd hs'_upd cont ((v, t, mapping)) in
              if Option.is_some state then state else None
          else None
        ) None hs in
      state

let classical_unify ?(match_whole = true) ?(tagpairs = true) ?(update_check = Fun._true) constraint_tags hs hs' cont init_state =
  let time = if !Stats.do_statistics then Stats.now() else 0. in
  let avoid_vars = (Term.Set.union (vars hs) (vars hs')) in
  let avoid_tags = (Tags.union (Tags.union (tags hs) (tags hs')) constraint_tags) in
  let hs, hs' = Pair.map (fun hs -> 
    let _, res = Blist.foldl (fun (index, res) h -> 
      (index + 1, res @ [(h, index)])
    ) (0, []) hs in
    res
  ) (hs, hs') in
  let res = classical_unify_rec ~match_whole ~tagpairs ~update_check
    avoid_vars avoid_tags
    hs hs' cont init_state
  in
  (if !Stats.do_statistics then
    Test_stats.unify_calls := !Test_stats.unify_calls + 1;
    Test_stats.unify_time := !Test_stats.unify_time +. (Stats.time_since time););
  match res with
    | None -> None
    | Some(res) -> cont res
  
let rec classical_biunify_rec ?(tagpairs = true) ?(update_check = Fun._true) avoid_vars avoid_tags hs hs' cont init_state =
  match hs' with
    | [] -> Some(init_state)
    | (h', index')::hs' ->
      let state = Blist.foldl
        (fun res (h, index) ->
          if Option.is_some res then res else
          let state = Heap.classical_biunify ~tagpairs ~update_check ~with_num:false h h' Unification.trivial_continuation init_state in
          if Option.is_some state then
            let (v, t, mapping), (v2, t2, mapping2) = Option.get state in
            let mapping = mapping @ [(index, index')] in
            let mapping2 = mapping2 @ [(index, index')] in
            let dif = h.Heap.num -. h'.Heap.num in
            let (hs_upd, hs'_upd, avoid_vars, avoid_tags) =
              if dif = 0. then
                (Blist.del_first (fun (_, i) -> i = index) hs, hs', avoid_vars, avoid_tags)
              else if dif > 0. then
                let h_upd = Heap.copy_fresh_heap (avoid_vars, avoid_tags) (Heap.with_num h dif) in
                (Blist.map (fun (h2, i) -> if i = index then (h_upd, i) else (h2, i)) hs,
                hs',
                Term.Set.union avoid_vars (Heap.vars h_upd),
                Tags.union avoid_tags (Heap.tags h_upd))
              else 
                let h'_upd = Heap.copy_fresh_heap (avoid_vars, avoid_tags) (Heap.with_num h' dif) in
                (Blist.del_first (fun (h2, i) -> i = index) hs,
                (h'_upd, index') :: hs',
                Term.Set.union avoid_vars (Heap.vars h'_upd),
                Tags.union avoid_tags (Heap.tags h'_upd))
            in
            let state = classical_biunify_rec ~tagpairs ~update_check avoid_vars avoid_tags hs_upd hs'_upd cont ((v, t, mapping), (v2, t2, mapping2)) in
            if Option.is_some state then state else None
          else None
        ) None hs in
      state

let classical_biunify ?(tagpairs = true) ?(update_check = Fun._true) constraint_tags hs hs' cont init_state =
  let time = if !Stats.do_statistics then Stats.now() else 0. in
  let avoid_vars = (Term.Set.union (vars hs) (vars hs')) in
  let avoid_tags = (Tags.union (Tags.union (tags hs) (tags hs')) constraint_tags) in
  let hs, hs' = Pair.map (fun hs -> 
    let _, res = Blist.foldl (fun (index, res) h -> 
      (index + 1, res @ [(h, index)])
    ) (0, []) hs in
    res
  ) (hs, hs') in
  let res = classical_biunify_rec ~tagpairs ~update_check
    avoid_vars avoid_tags
    hs hs' cont init_state
  in
  (if !Stats.do_statistics then
    Test_stats.unify_calls := !Test_stats.unify_calls + 1;
    Test_stats.unify_time := !Test_stats.unify_time +. (Stats.time_since time););
  match res with
    | None -> None
    | Some(res) -> cont res