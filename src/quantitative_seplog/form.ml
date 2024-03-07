open Lib
open   Symbols

open Generic

open MParser

include Pair.Make (Tags.Elt) (Pair.Make (Ord_constraints) (Flist.Make (Heapsum)))

let empty = (Tags.anonymous, (Ord_constraints.empty, [[Heap.empty]]))

exception Not_symheap
exception Not_symheap_sum

let is_symheap = function _, (_, [[s]]) -> true | _ -> false

let dest : t -> Ord_constraints.t * Heap.t = function
  | _, (cs, [s]) -> (cs, Heapsum.dest s)
  | _ -> raise Not_symheap

let dest_sum : t -> Ord_constraints.t * Heapsum.t = function
  | _, (cs, [s]) -> (cs, s)
  | _ -> raise Not_symheap_sum

let constraints_sep cs =
  if Ord_constraints.is_empty cs then symb_nullstr else symb_colon

let pp fmt (t, (cs, f)) =
  let pp_or fmt () = Format.fprintf fmt " %s@ " symb_or.str in
  let tag_str = if Tags.is_anonymous t then "" else "[" ^ (Tags.Elt.to_string t) ^ "] " in
  match f with
  | [] ->
      Format.fprintf fmt "@[%a%s%s%s@]" Ord_constraints.pp cs
        (constraints_sep cs).sep tag_str symb_false.str
  | _ ->
      Format.fprintf fmt "@[%a%s%s%a@]" Ord_constraints.pp cs
        (constraints_sep cs).sep
        tag_str
        (Blist.pp pp_or Heapsum.pp)
        f

let to_string (t, (cs, hs)) =
  let cs_str = Ord_constraints.to_string cs ^ (constraints_sep cs).sep in
  let tag_str = if Tags.is_anonymous t then "" else "[" ^ (Tags.Elt.to_string t) ^ "] " in
  match hs with
  | [] -> cs_str ^ tag_str ^ symb_false.str
  | hs -> cs_str ^ tag_str ^ Blist.to_string symb_or.sep Heapsum.to_string hs

let terms (_, (_, d)) = Term.Set.union_of_list (Blist.map Heapsum.terms d)

let vars f = Term.filter_vars (terms f)

let tags (t, (cs, _)) =
  Tags.union_of_list (Ord_constraints.tags cs :: [Tags.of_list [t]])

let tag_pairs f = Tagpairs.mk (tags f)

let tags_wo_constraints (t, (_, _)) =
  Tags.of_list [t]

let tag_pairs_wo_constraints f = Tagpairs.mk (tags_wo_constraints f)

let tag_pairs_custom t = Tagpairs.mk (Tags.of_list [t])

let inconsistent (_, (cs, f)) =
  Ord_constraints.inconsistent cs || Blist.for_all Heapsum.inconsistent f

let complete_tags avoid (t, (cs, fs)) =
  let t =
    if Tags.is_anonymous t then
      let avoid' = Tags.union (Ord_constraints.tags cs) avoid in
      Tags.fresh_evar avoid'
    else t
  in
  (t, (cs, fs))

let subsumed_upto_constraints ?(total = true) (_, (_, f)) (_, (_, f')) =
  Blist.for_all
    (fun d2 -> Blist.exists (fun d1 -> Heapsum.subsumed ~total d1 d2) f)
    f'

let subsumed ?(total = true) ((_, (cs, _)) as l) ((_, (cs', _)) as r) =
  subsumed_upto_constraints ~total l r
  &&
  let () =
    debug (fun _ ->
        "Checking constraint subsumption: "
        ^ Ord_constraints.to_string cs'
        ^ " |- "
        ^ Ord_constraints.to_string cs )
  in
  let cs' = Ord_constraints.close cs' in
  Ord_constraints.subsumes cs' cs

let equal_upto_tags (_, (cs, hs)) (_, (cs', hs')) =
  Blist.for_all2 Heapsum.equal hs hs'

(*let tag_parse st = 
  (parse_symb (make_symb "[") >>= return Tags.Elt.parse >>= parse_symb (make_symb "]") << spaces
  >>= fun t ->
    return t)
  st*)

let parse ?(null_is_emp = false) ?(allow_tags = true) ?(augment_deqs = true) st (*TODO test parsing of tags*)
    =
  ( (if allow_tags then option Ord_constraints.parse else return None)
  >>= fun cs ->
  (if allow_tags then option Tags.Elt.parse else return None)
  >>= fun t ->
  sep_by (Heapsum.parse ~augment_deqs) (parse_symb symb_or)
  <?> "formula"
  >>= fun hs ->
  return
    (Option.dest Tags.anonymous Fun.id t,
    ( Option.dest Ord_constraints.empty Fun.id cs
    , if null_is_emp && Blist.is_empty hs then [] else hs )) )
    st

let of_string ?(null_is_emp = false) s =
  handle_reply (MParser.parse_string (parse ~null_is_emp) s ())

let star ?(augment_deqs = true) (_, (cs, f)) (_, (cs', g)) =
  let constraints = Ord_constraints.union cs cs' in
  (Tags.anonymous, (constraints, Blist.map (
    fun (f', g') ->
      Heapsum.star ~augment_deqs f' g')
    (Blist.cartesian_product f g)))

let disj (_, (cs, f)) (_, (cs', g)) = (Tags.anonymous, (Ord_constraints.union cs cs', f @ g))

let subst theta (t, (cs, hs)) = (t, (cs, Blist.map (fun h -> Heapsum.subst theta h) hs))

let subst_existentials (t, (cs, hs)) = (t, (cs, Blist.map Heapsum.subst_existentials hs))

let subst_tags tagpairs (t, (cs, hs)) =
  (Tagpairs.apply_to_tag tagpairs t, ( Ord_constraints.subst_tags tagpairs cs, hs ))

let norm (t, (cs, hs)) = (t, (cs, Blist.map Heapsum.norm hs))

let with_constraints (t, (_, hs)) cs = (t, (cs, hs))

let with_heapsums (t, (cs, _)) hs = (t, (cs, hs))

let add_constraints (t, (cs, hs)) cs' = (t, (Ord_constraints.union cs cs', hs))

let get_tracepairs f ((_, (cs, _)) as f') =
  let cs = Ord_constraints.close cs in
  let id_pairs = Tagpairs.mk (Pair.apply Tags.inter (Pair.map tags (f, f'))) in
  let allpairs, progressing =
    Pair.map
      (fun tps ->
        Tagpairs.map Pair.swap
          (Tagpairs.filter (fun (_, t) -> Tags.mem t (tags f)) tps) )
      ( Tagpairs.union id_pairs (Ord_constraints.all_pairs cs)
      , Ord_constraints.prog_pairs cs )
  in
  (allpairs, progressing)


let mk_heap h =
  (Tags.anonymous, (Ord_constraints.empty, [[h]]))

let mk_heapsums hss =
  (Tags.anonymous, (Ord_constraints.empty, hss))

let rec is_boolean ?(covered = []) defs (_, (_, hss)) =
  let defs' = Blist.map (fun def -> Preddef.dest def) defs in
  Blist.for_all (fun hs -> 
    match hs with
      | h :: [] ->
        (h.Heap.num = (0,0) || h.Heap.num = (1,0))
        && Tpreds.for_all (fun (_, (ident, _)) ->
          if Blist.mem ident covered then true else
            let cases = Blist.flatten (Blist.filter_map (fun (def, (sym, _)) -> if sym = ident then Some(Preddef.rules_heapsums def) else None) defs') in
            let covered = covered @ [ident] in
            Blist.for_all (fun case ->
              is_boolean ~covered:covered defs (mk_heapsums [case])
            ) cases
        ) h.Heap.inds
      | [] -> true
      | _ -> false
  ) hss

let rec is_natural_least_one ?(covered = []) defs (_, (_, hss)) =
  let defs' = Blist.map (fun def -> Preddef.dest def) defs in
  Blist.for_all (fun hs -> 
    Blist.for_all (fun h -> 
      (snd h.Heap.num <= 0 || Num.get_int h.Heap.num >= 1)
      && Tpreds.for_all (fun (_, (ident, _)) ->
        if Blist.mem ident covered then true else
          let cases = Blist.flatten (Blist.filter_map (fun (def, (sym, _)) -> if sym = ident then Some(Preddef.rules_heapsums def) else None) defs') in
          let covered = covered @ [ident] in
          Blist.for_all (fun case ->
            is_natural_least_one ~covered:covered defs (mk_heapsums [case])
          ) cases
      ) h.Heap.inds
    ) hs
  ) hss

let rec is_non_empty_derivable ?(covered = []) defs (_, (_, hss)) = 
  let defs' = Blist.map (fun def -> Preddef.dest def) defs in
  Blist.for_all (fun hs ->
    Blist.for_all (fun h ->
      h.Heap.num = (0,0)
      || not (Ptos.is_empty h.Heap.ptos)
      || (not (Tpreds.is_empty h.Heap.inds) && Tpreds.for_all (fun (_, (ident, _)) -> 
        if Blist.mem ident covered then true else
          let cases = Blist.flatten (Blist.filter_map (fun (def, (sym, _)) -> if sym = ident then Some(Preddef.rules_heapsums def) else None) defs') in
          let covered = covered @ [ident] in
          Blist.for_all (fun case -> 
            is_non_empty_derivable ~covered:covered defs (mk_heapsums [case])
          ) cases  
      ) h.Heap.inds)
    ) hs
  ) hss

let is_precise defs (_, (_, hss)) = 
  let defs' = Blist.map (fun def ->
    let (indrules, a) = Preddef.dest def in
    let rules = Blist.map (fun rule -> Indrule.dest rule) indrules in
    (rules, a)
  ) defs in
  match hss with
    | hs :: [] -> Heapsum.is_precise defs' hs
    | [] -> true
    | _ -> false

let set_precise_preds defs (tag, (cs, hss)) =
  let defs' = Blist.map (fun def -> Preddef.dest def) defs in
  (tag, (cs, Blist.map (fun hs ->
    Blist.map (fun h ->
      Heap.with_inds h (Tpreds.map (fun (precise, (ident, args)) ->
        let precise_def = Blist.filter_map (fun (_, (sym, (precise, _))) -> if sym = ident then Some(precise > 0) else None) defs' in
        if Blist.for_all (fun b -> b) precise_def then
          if Blist.for_all (fun arg -> not (Term.is_exist_var arg)) args then (1, (ident, args))
          else (0, (ident, args))
        else (-1, (ident, args))
      ) h.Heap.inds)
    ) hs  
  ) hss ))

let reduce_zeros (tag, (cs, hss)) =
  (tag, (cs, Blist.foldl (fun list hs ->
    let hs = Blist.foldl (fun res h ->
      if h.Heap.num = (0,0) then res else res @ [h]
    ) [] hs in
    if Blist.length hs = 0 then list else list @ [hs]
  ) [] hss ))