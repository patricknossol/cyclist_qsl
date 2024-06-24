open Lib
open Symbols
open Qsl_symbols

open Generic

open MParser

include Flist.Make (Heap)

exception Not_symheap

let empty = []

let is_empty hs = hs = empty

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

let inconsistent hs =
  Blist.for_all Heap.inconsistent hs

let rec subsumed_rec ?(total = true) hs hs' =
  match hs with
    | [] -> true
    | h::hs ->
      let res = Blist.foldl
        (fun res h' ->
          if res then res else
          let res = Heap.subsumed ~total ~with_num:false h h' in
          if res then
            let dif = (Num.get_int h.Heap.num) - (Num.get_int h'.Heap.num) in
            let (hs_upd, hs'_upd) =
              if dif = 0 then
                (hs, Blist.del_first (fun h2 -> h2 = h') hs')
              else if dif > 0 then
                (Heap.with_num h (dif,0) :: hs, Blist.del_first (fun h2 -> h2 = h') hs')
              else 
                (hs, Blist.map (fun h2 -> if h2 = h' then Heap.with_num h' (dif,0) else h2) hs')
            in
            subsumed_rec ~total hs_upd hs'_upd
          else false
        ) false hs' in
      res

let subsumed ?(total = true) hs hs' =
  let time = if !Stats.do_statistics then Stats.now() else 0. in
  let res = subsumed_rec ~total hs hs' in
  (if !Stats.do_statistics then
    Test_stats.unify_calls := !Test_stats.unify_calls + 1;
    Test_stats.unify_time := !Test_stats.unify_time +. (Stats.time_since time););
  res

let equal hs hs' =
  Blist.for_all2 Heap.equal hs hs'

let parse ?(augment_deqs = true) st =
  (sep_by (Heap.parse ~augment_deqs) (parse_symb symb_plus)
  >>= (fun hs ->
  return
    hs) <?> "heapsum")
    st

let of_string s =
  handle_reply (MParser.parse_string (parse ~augment_deqs:true) s ())

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

let univ s hs =
  let v = (Term.Set.union s (vars hs)) in
  let (res, _) = Blist.foldl (fun (res, v) h -> 
    let h = Heap.univ v h in
    (res @ [h], Term.Set.union v (Heap.vars h))
  ) ([], v) hs in
  res

let norm hs = Blist.map Heap.norm hs

let equates hs a b =
  Blist.for_all (fun h -> Heap.equates h a b) hs

let disequates hs a b =
    Blist.for_all (fun h -> Heap.disequates h a b) hs

let ptos_filter_map f ptos =
  Ptos.fold (fun pto res -> 
    let r = f pto in
    if Option.is_none r then res
    else res @ [Option.get r]
  ) ptos []

let rec list_union (l1:'a list) (l2:'a list) =
  let rec f x l = match l with
    | [] -> true
    | hd::tl ->
      if x = hd then false else f x tl
    in
  match l2 with
  | [] -> l1
  | hd::tl ->
    if f hd l1 then
      list_union (hd::l1) tl
    else
      list_union l1 tl

let rec calc_fixed_vars fixed_vars h = 
  let new_vars = ptos_filter_map ( fun (v, _) ->
    if Term.is_exist_var v then
      if Term.Set.exists (fun v2 ->
        let fixed_xs = ptos_filter_map (fun (x, x2) -> if Blist.exists (fun x2 -> x2 = v2) x2 && Blist.mem x fixed_vars then Some(x) else None) h.Heap.ptos in
        Uf.equates h.Heap.eqs v v2
        && (
          (Blist.mem v2 fixed_vars)
          || (Blist.length fixed_xs > 0)
        )
      ) (Heap.vars h) then
        Some(v)
      else None
    else None
  ) h.Heap.ptos in
  let new_fixed_vars = list_union fixed_vars new_vars in
  if (Blist.length new_fixed_vars) = (Blist.length fixed_vars) then
    new_fixed_vars
  else
    calc_fixed_vars new_fixed_vars h

let is_precise defs' hs =
  match hs with
    | h :: [] ->
      let precise_preds = Tpreds.for_all ( fun ((_, ((ident, _), _)) as pred) ->
        let precise_def = Blist.filter_map (fun (_, (sym, (precise, _))) -> if sym = ident then Some(precise > 0) else None) defs' in
        Tpred.precise_tag pred
        || (
          Blist.for_all ( fun arg ->
            not (Term.is_exist_var arg)
          ) (Tpred.args pred)
          &&  Blist.for_all (fun b -> b) precise_def
        )
      ) h.Heap.inds in
      let left_ex_vars = ptos_filter_map (fun (v, _) ->
        if Term.is_exist_var v then Some(v) else None
      ) h.Heap.ptos in
      let left_fixed_vars = ptos_filter_map (fun (v, _) ->
        if not (Term.is_exist_var v) || Term.Set.exists (fun v2 -> not (Term.is_exist_var v2) && Heap.equates h v v2) (Heap.vars h) then Some(v) else None
      ) h.Heap.ptos in
      let fixed_vars = calc_fixed_vars left_fixed_vars h in
      let precise_ptos = Blist.for_all (fun v -> Blist.mem v fixed_vars) left_ex_vars in
      precise_preds && precise_ptos
    | [] -> true
    | _  -> false

(*frame or hs precise or hs one summand*)
let frame_sum_conditions_met frame hs defs =
  Blist.length hs <= 1 || is_precise defs [frame] || is_precise defs hs

let do_frames_match frame frame' =
  let free_vars = Term.Set.filter (fun t -> not (Term.is_exist_var t)) (Heap.vars frame) in
  let free_vars' = Term.Set.filter (fun t -> not (Term.is_exist_var t)) (Heap.vars frame') in
  let upd_chk = Unify.Unidirectional.avoid_replacing_trms (Term.Set.union free_vars free_vars') in
  let state = Heap.classical_unify ~update_check:upd_chk ~with_num:false frame frame' Unification.trivial_continuation Unify.Unidirectional.empty_state in
  let state' = Heap.classical_unify ~update_check:upd_chk ~with_num:false frame' frame Unification.trivial_continuation Unify.Unidirectional.empty_state in
  Option.is_some state && Option.is_some state'

let rec unify_partial_rec ?(frame = None) ?(update_check = Fun._true) ?(matched_hs' = []) defs avoid_vars hs hs' cont init_state =
  match hs with
  | [] -> 
    if Option.is_none frame || frame_sum_conditions_met (Option.get frame) matched_hs' defs
    then Some(init_state) else None
  | (h, index) :: hs ->
    let state = Blist.foldl
      (fun res (h', index') ->
        if Option.is_some res then res else
        let () = debug (fun _ -> "pa - h: " ^ (Heap.to_string h) ^ " | h': " ^ (Heap.to_string h')) in
        let state = Heap.unify_partial ~update_check ~with_num:false h h' Unification.trivial_continuation init_state in
        let () = debug (fun _ -> "state: " ^ (string_of_bool (Option.is_some state))) in
        if Option.is_some state then
          let (v, t, mapping) = Option.get state in
          (*Calc frame = h' - theta(h) (only inds, ptos) and check if frames match and prerequisites for rules are fulfilled*)
          let (frame', rest) = Heap.calc_spatial_frame (Heap.subst v h) h' in
          let () = debug (fun _ -> "frame': " ^ (Heap.to_string frame') ^ " | rest: " ^ (Heap.to_string rest)) in
          if Option.is_some frame && not (do_frames_match (Option.get frame) frame')
          then None else
          let () = debug (fun _ -> "hiii2") in
          let mapping = mapping @ [(index, index')] in
          let dif = (Num.get_int h.Heap.num) - (Num.get_int h'.Heap.num) in
          let (matched_hs'_upd, hs_upd, hs'_upd, avoid_vars) =
            if dif = 0 then
              (matched_hs' @ [rest], Blist.del_first (fun (_, i) -> i = index) hs, hs', avoid_vars)
            else if dif > 0 then
              let h_upd = Heap.copy_fresh_heap avoid_vars (Heap.with_num h (dif,0)) in
              (matched_hs', Blist.map (fun (h2, i) -> if i = index then (h_upd, i) else (h2, i)) hs,
              hs',
              Term.Set.union avoid_vars (Heap.vars h_upd))
            else 
              let h'_upd = Heap.copy_fresh_heap avoid_vars (Heap.with_num h' (dif,0)) in
              (matched_hs', Blist.del_first (fun (h2, i) -> i = index) hs,
              (h'_upd, index') :: hs',
              Term.Set.union avoid_vars (Heap.vars h'_upd))
          in
          let frame' = Some(frame') in
          let state = unify_partial_rec ~frame:frame' ~update_check ~matched_hs':matched_hs'_upd defs avoid_vars hs_upd hs'_upd cont (v, t, mapping) in
          if Option.is_some state then state else None
        else None
      ) None hs' in
    state

let unify_partial ?(update_check = Fun._true) defs hs hs' cont init_state =
  let time = if !Stats.do_statistics then Stats.now() else 0. in
  let avoid_vars = (Term.Set.union (vars hs) (vars hs')) in
  let hs, hs' = Pair.map (fun hs -> 
    let _, res = Blist.foldl (fun (index, res) h -> 
      (index + 1, res @ [(h, index)])
    ) (0, []) hs in
    res
  ) (hs, hs') in
  let res = unify_partial_rec ~update_check
    defs avoid_vars
    hs hs' cont init_state
  in
  (if !Stats.do_statistics then
    Test_stats.unify_calls := !Test_stats.unify_calls + 1;
    Test_stats.unify_time := !Test_stats.unify_time +. (Stats.time_since time););
  match res with
    | None -> None
    | Some(res) -> cont res

let rec classical_unify_rec ?(allow_conform = false) ?(match_whole = true) ?(update_check = Fun._true) avoid_vars hs hs' cont init_state =
  (*hs' = ls, hs = rs*)
  match hs' with
    | [] -> Some(init_state)
    | (h', index')::hs' ->
      let state = Blist.foldl
        (fun res (h, index) ->
          if Option.is_some res then res else
          let state = Heap.classical_unify ~allow_conform ~update_check ~with_num:false h h' Unification.trivial_continuation init_state in
          if Option.is_some state then
            let (v, t, mapping) = Option.get state in
            let mapping = mapping @ [(index, index')] in
            if not match_whole then
              Some(v, t, mapping)
            else
              let dif = (Num.get_int h.Heap.num) - (Num.get_int h'.Heap.num) in
              let (hs_upd, hs'_upd, avoid_vars) =
                if dif = 0 then
                  (Blist.del_first (fun (_, i) -> i = index) hs, hs', avoid_vars)
                else if dif > 0 then
                  let h_upd = Heap.copy_fresh_heap avoid_vars (Heap.with_num h (dif,0)) in
                  (Blist.map (fun (h2, i) -> if i = index then (h_upd, i) else (h2, i)) hs,
                  hs',
                  Term.Set.union avoid_vars (Heap.vars h_upd))
                else 
                  let h'_upd = Heap.copy_fresh_heap avoid_vars (Heap.with_num h' (dif,0)) in
                  (Blist.del_first (fun (h2, i) -> i = index) hs,
                  (h'_upd, index') :: hs',
                  Term.Set.union avoid_vars (Heap.vars h'_upd))
              in
              let state = classical_unify_rec ~update_check avoid_vars hs_upd hs'_upd cont ((v, t, mapping)) in
              if Option.is_some state then state else None
          else None
        ) None hs in
      state

let classical_unify ?(allow_conform = false) ?(match_whole = true) ?(update_check = Fun._true) hs hs' cont init_state =
  let time = if !Stats.do_statistics then Stats.now() else 0. in
  let avoid_vars = (Term.Set.union (vars hs) (vars hs')) in
  let hs, hs' = Pair.map (fun hs -> 
    let _, res = Blist.foldl (fun (index, res) h -> 
      (index + 1, res @ [(h, index)])
    ) (0, []) hs in
    res
  ) (hs, hs') in
  let res = classical_unify_rec ~allow_conform ~match_whole ~update_check
    avoid_vars
    hs hs' cont init_state
  in
  (if !Stats.do_statistics then
    Test_stats.unify_calls := !Test_stats.unify_calls + 1;
    Test_stats.unify_time := !Test_stats.unify_time +. (Stats.time_since time););
  match res with
    | None -> None
    | Some(res) -> cont res
  
let rec classical_biunify_rec ?(frame = None) ?(update_check = Fun._true) ?(matched_hs = []) avoid_vars hs hs' cont init_state =
  match hs' with
    | [] -> 
      (*if Option.is_none frame || frame_sum_conditions_met (Option.get frame) matched_hs
      then Some(init_state) else None*)
      Some(init_state)
    | (h', index')::hs' ->
      let state = Blist.foldl
        (fun res (h, index) ->
          if Option.is_some res then res else
          let () = debug (fun _ -> "bi - h: " ^ (Heap.to_string h) ^ " | h': " ^ (Heap.to_string h')) in
          let state = Heap.classical_biunify ~update_check ~with_num:false h h' Unification.trivial_continuation init_state in
          if Option.is_some state then
            let (v, t, mapping), (v2, t2, mapping2) = Option.get state in
            let (frame', rest) = Heap.calc_spatial_frame h' (Heap.subst v h) in
            (*if Option.is_none frame && not (frame_rule_conditions_met frame')
              || Option.is_some frame && not (do_frames_match (Option.get frame) frame')
            then None else*)
            let () = debug (fun _ -> "hiii3") in
            let mapping = mapping @ [(index, index')] in
            let mapping2 = mapping2 @ [(index, index')] in
            let dif = (Num.get_int h.Heap.num) - (Num.get_int h'.Heap.num) in
            let (matched_hs_upd, hs_upd, hs'_upd, avoid_vars) =
              if dif = 0 then
                (matched_hs @ [rest], Blist.del_first (fun (_, i) -> i = index) hs, hs', avoid_vars)
              else if dif > 0 then
                let h_upd = Heap.copy_fresh_heap avoid_vars (Heap.with_num h (dif,0)) in
                (matched_hs, Blist.map (fun (h2, i) -> if i = index then (h_upd, i) else (h2, i)) hs,
                hs',
                Term.Set.union avoid_vars (Heap.vars h_upd))
              else 
                let h'_upd = Heap.copy_fresh_heap avoid_vars (Heap.with_num h' (dif,0)) in
                (matched_hs, Blist.del_first (fun (h2, i) -> i = index) hs,
                (h'_upd, index') :: hs',
                Term.Set.union avoid_vars (Heap.vars h'_upd))
            in
            let frame' = Some(frame') in
            let state = classical_biunify_rec ~frame:frame' ~update_check ~matched_hs:matched_hs_upd avoid_vars hs_upd hs'_upd cont ((v, t, mapping), (v2, t2, mapping2)) in
            if Option.is_some state then state else None
          else None
        ) None hs in
      state

let classical_biunify ?(update_check = Fun._true) hs hs' cont init_state =
  let time = if !Stats.do_statistics then Stats.now() else 0. in
  let avoid_vars = (Term.Set.union (vars hs) (vars hs')) in
  let hs, hs' = Pair.map (fun hs -> 
    let _, res = Blist.foldl (fun (index, res) h -> 
      (index + 1, res @ [(h, index)])
    ) (0, []) hs in
    res
  ) (hs, hs') in
  let res = classical_biunify_rec ~update_check
    avoid_vars
    hs hs' cont init_state
  in
  (if !Stats.do_statistics then
    Test_stats.unify_calls := !Test_stats.unify_calls + 1;
    Test_stats.unify_time := !Test_stats.unify_time +. (Stats.time_since time););
  match res with
    | None -> None
    | Some(res) -> cont res