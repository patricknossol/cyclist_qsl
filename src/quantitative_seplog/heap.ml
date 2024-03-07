open Lib
open   Symbols

open Generic

open MParser

let split_heaps = ref true

type abstract1 = Term.Set.t option

type abstract2 = Tags.t option

type symheap =
  { eqs: Uf.t
  ; deqs: Deqs.t
  ; ptos: Ptos.t
  ; inds: Tpreds.t
  ; num: Num.t
  ; mutable _terms: Term.Set.t option
  ; mutable _vars: Term.Set.t option }

type t = symheap

(* accessors *)

let equal h h' =
  h == h'
  || Uf.equal h.eqs h'.eqs
     && Deqs.equal h.deqs h'.deqs
     && Ptos.equal h.ptos h'.ptos
     && Tpreds.equal h.inds h'.inds
     && Num.equal h.num h'.num

let equal_upto_num h h' =
  h == h'
  || Uf.equal h.eqs h'.eqs
      && Deqs.equal h.deqs h'.deqs
      && Ptos.equal h.ptos h'.ptos
      && Tpreds.equal h.inds h'.inds

include Fixpoint.Make (struct
  type t = symheap

  let equal = equal
end)

let compare f g =
  if f == g then 0
  else
    match Uf.compare f.eqs g.eqs with
    | n when not (Int.equal n 0) -> n
    | _ -> (
      match Deqs.compare f.deqs g.deqs with
      | n when not (Int.equal n 0) -> n
      | _ -> (
        match Ptos.compare f.ptos g.ptos with
        | n when not (Int.equal n 0) -> n
        | _ -> (
          match Tpreds.compare f.inds g.inds with
        | n when not (Int.equal n 0) -> n
        | _ -> (
          Num.compare f.num g.num
      ) ) ) )

(* custom hash function so that memoization fields are ignored when hashing *)
(* so that the hash invariant is preserved [a = b => hash(a) = hash(b)] *)
(* FIXME: memoize hash as well? *)
let hash h =
  genhash
    (genhash
       (genhash 
          (genhash (Tpreds.hash h.inds) (Ptos.hash h.ptos))
          (Num.hash h.num))
       (Deqs.hash h.deqs))
    (Uf.hash h.eqs)

let terms f =
  match f._terms with
  | Some trms -> trms
  | None ->
      let trms =
        Term.Set.union_of_list
          [ Uf.terms f.eqs
          ; Deqs.terms f.deqs
          ; Ptos.terms f.ptos
          ; Tpreds.terms f.inds ]
      in
      f._terms <- Some trms ;
      trms

let vars f =
  match f._vars with
  | Some v -> v
  | None ->
      let v = Term.filter_vars (terms f) in
      f._vars <- Some v ;
      v

let to_string f =
  let res =
    (String.concat symb_star.sep
      ( Uf.to_string_list f.eqs
      @ Deqs.to_string_list f.deqs
      @ Ptos.to_string_list f.ptos
      @ Tpreds.to_string_list f.inds
      @ [Num.to_string f.num] ))
  in
  if String.equal res "" then keyw_emp.str else res

let pp fmt h =
  let l =
    Uf.to_string_list h.eqs
    @ Deqs.to_string_list h.deqs
    @ Ptos.to_string_list h.ptos
    @ Tpreds.to_string_list h.inds
    @ [Num.to_string h.num]
  in
  Format.fprintf fmt "@[%a@]"
    (Blist.pp pp_star Format.pp_print_string)
    (if not (Blist.is_empty l) then l else [keyw_emp.str])

let equates h x y = Uf.equates h.eqs x y

let disequates h x y =
  Deqs.exists
    (fun (w, z) ->
      (equates h x w && equates h y z) || (equates h x z && equates h y w) )
    h.deqs

let find_lval x h = Ptos.find_opt (fun (y, _) -> equates h x y) h.ptos

let inconsistent h =
  Deqs.exists (Fun.uncurry Term.equal) h.deqs
  || Deqs.exists (fun (x, y) -> equates h x y) h.deqs

let idents p = Tpreds.idents p.inds

let subsumed ?(total = true) ?(with_num = true) h h' =
  (not with_num || Num.subsumed h.num h'.num)
  && Uf.subsumed h.eqs h'.eqs
  && Deqs.subsumed h'.eqs h.deqs h'.deqs
  && Ptos.subsumed ~total h'.eqs h.ptos h'.ptos
  && Tpreds.subsumed ~total h'.eqs h.inds h'.inds

(* Constructors *)

let empty = {eqs=Uf.empty; deqs=Deqs.empty; ptos=Ptos.empty; inds=Tpreds.empty; num=(1,0); _terms= None; _vars= None}

let empty_not_form = {eqs=Uf.empty; deqs=Deqs.empty; ptos=Ptos.empty; inds=Tpreds.empty; num=Num.empty; _terms= None; _vars= None}

let fix_empty_num h =
  if not (equal h empty_not_form) && Num.is_empty h.num then
    {eqs=h.eqs; deqs=h.deqs; ptos=h.ptos; inds=h.inds; num=(1,0); _terms=h._terms; _vars=h._vars}
  else h

let mk eqs deqs ptos inds num =
  fix_empty_num {eqs; deqs; ptos; inds; num; _terms= None; _vars= None}

let dest h = (h.eqs, h.deqs, h.ptos, h.inds, h.num)

let is_empty h = equal h empty

let subst theta h =
  { eqs= Uf.subst theta h.eqs
  ; deqs= Deqs.subst theta h.deqs
  ; ptos= Ptos.subst theta h.ptos
  ; inds= Tpreds.subst theta h.inds
  ; num= h.num
  ; _terms= None
  ; _vars= None }

let with_eqs h eqs = fix_empty_num {h with eqs; _terms= None; _vars= None}

let with_deqs h deqs = fix_empty_num {h with deqs; _terms= None; _vars= None}

let with_ptos h ptos = fix_empty_num {h with ptos; _terms= None; _vars= None}

let with_inds h inds = fix_empty_num (mk h.eqs h.deqs h.ptos inds h.num)

let with_num h num = fix_empty_num (mk h.eqs h.deqs h.ptos h.inds num)

let del_deq h deq = with_deqs h (Deqs.del_first (fun deq' -> deq = deq') h.deqs)

let del_pto h pto = with_ptos h (Ptos.del_first (fun pto' -> pto' = pto) h.ptos)

let del_num h num = with_num h Num.empty

let del_ind h ind =
  { h with
    inds= Tpreds.remove ind h.inds; _terms= None; _vars= None
  }

let mk_pto pto =
  fix_empty_num { empty with
    ptos= Ptos.singleton pto; _terms= None; _vars= None }

let mk_eq p =
  fix_empty_num { empty with
    eqs= Uf.add p Uf.empty; _terms= None; _vars= None }

let mk_deq p =
  fix_empty_num {empty with deqs= Deqs.singleton p; _terms= None; _vars= None}

let mk_ind pred =
  fix_empty_num { empty with
    inds= Tpreds.singleton pred; _terms= None; _vars= None }

let mk_num num =
  {empty with
  num = num;  _terms= None; _vars= None}

(* computes all deqs due to a list of ptos *)
let explode_deqs h =
  let ptos = Ptos.elements h.ptos in
  let cp = Blist.cartesian_hemi_square ptos in
  let s1 =
    Blist.fold_left
      (fun s p -> Deqs.add (fst p, Term.nil) s)
      Deqs.empty ptos
  in
  let new_deqs =
    Blist.fold_left (fun s (p, q) -> Deqs.add (fst p, fst q) s) s1 cp
  in
  with_deqs h (Deqs.union h.deqs new_deqs)

(* star two formulae together *)
let star ?(augment_deqs = true) f g =
  let h =
    mk (Uf.union f.eqs g.eqs)
      (Deqs.union f.deqs g.deqs)
      (Ptos.union f.ptos g.ptos)
      (Tpreds.union f.inds g.inds)
      (Num.mul f.num g.num)
  in
  if augment_deqs then explode_deqs h else h

let parse_atom st =
  ( attempt (parse_symb keyw_emp >>$ empty)
  <|> attempt (Num.parse |>> mk_num)
  <|> attempt (Tpred.parse |>> mk_ind)
  <|> attempt (Uf.parse |>> mk_eq)
  <|> attempt (Deqs.parse |>> mk_deq)
  <|> (Pto.parse |>> mk_pto) <?> "atom" )
    st

let parse ?(augment_deqs = true) st =
  ( sep_by1 parse_atom (parse_symb symb_star)
  >>= (fun atoms -> return (Blist.foldl (star ~augment_deqs) empty atoms))
  <?> "symheap" )
    st

let of_string ?(augment_deqs = true) s =
  handle_reply (MParser.parse_string (parse ~augment_deqs) s ())

let add_eq h eq =
  fix_empty_num {h with eqs= Uf.add eq h.eqs; _terms= None; _vars= None}

let add_deq h deq =
  fix_empty_num {h with deqs= Deqs.add deq h.deqs; _terms= None; _vars= None}

let add_pto h pto = star h (mk_pto pto)

let add_ind h ind = with_inds h (Tpreds.add ind h.inds)

let univ s f =
  let vs = vars f in
  let theta =
    Subst.mk_free_subst (Term.Set.union s vs)
      (Term.Set.filter Term.is_exist_var vs)
  in
  if Term.Map.is_empty theta then f else subst theta f

let subst_existentials h =
  let aux h =
    try
      let eqs = Uf.bindings h.eqs in
      let ((x, y) as eq) =
        Blist.find (fun eq -> Pair.disj (Pair.map Term.is_exist_var eq)) eqs
      in
      let eqs = Blist.filter (fun eq' -> eq' != eq) eqs in
      let x, y = if Term.is_exist_var x then eq else (y, x) in
      let h' =
        {h with eqs= Uf.of_list eqs; _terms= None; _vars= None}
      in
      subst (Term.Map.singleton x y) h'
    with Not_found -> h
  in
  fixpoint aux h

let norm h =
  { h with
    deqs= Deqs.norm h.eqs h.deqs
  ; ptos= Ptos.norm h.eqs h.ptos
  ; inds= Tpreds.norm h.eqs h.inds
  ; num= h.num
  ; _terms= None
  ; _vars= None }

(* tags and unification *)

let copy_fresh_heap vars_avoid h =
  let vars_avoid = Term.Set.filter (fun var -> Term.is_exist_var var) vars_avoid in
  let h_vars = Term.Set.filter (fun var -> Term.is_exist_var var) (vars h) in
  let theta = Subst.avoid vars_avoid h_vars in
  subst theta h
  

let unify_partial ?(update_check = Fun._true) ?(with_num = true) h h' cont
    init_state =
  if not with_num || Num.subsumed h.num h'.num then
    (Tpreds.unify ~total:false ~update_check h.inds h'.inds
      (Ptos.unify ~total:false ~update_check h.ptos h'.ptos
        (Deqs.unify_partial ~update_check h.deqs h'.deqs
            (Uf.unify_partial ~update_check h.eqs h'.eqs cont))))
    init_state
  else None

let classical_unify ?(inverse = false) 
  ?(update_check = Fun._true)  ?(with_num = true) h h' cont init_state =  
  if not with_num || Num.subsumed h.num h'.num then
    let h_inv, h'_inv = Fun.direct inverse Pair.mk h h' in
(* NB how we don't need an "inverse" version for ptos and inds, since *)
(* we unify the whole multiset, not a subformula *)
    (Tpreds.unify ~update_check h_inv.inds h'_inv.inds
      (Ptos.unify ~update_check h_inv.ptos h'_inv.ptos
          (Deqs.unify_partial ~inverse ~update_check h.deqs h'.deqs
            (Uf.unify_partial ~inverse ~update_check h.eqs h'.eqs cont))))
    init_state
  else None

let classical_biunify ?(update_check = Fun._true) ?(with_num = true) h h' cont
  init_state =
  if not with_num || Num.subsumed h.num h'.num then
    (Tpreds.biunify ~update_check h.inds h'.inds
      (Ptos.biunify ~update_check h.ptos h'.ptos
          (Deqs.biunify_partial ~update_check h.deqs h'.deqs
            (Uf.biunify_partial ~update_check h.eqs h'.eqs cont))))
    init_state
  else None

let all_subheaps h =
  let all_ptos = Ptos.subsets h.ptos in
  let all_preds = Tpreds.subsets h.inds in
  let all_deqs = Deqs.subsets h.deqs in
  let all_ufs =
    Blist.map
      (fun xs -> Blist.foldr Uf.remove xs h.eqs)
      (Blist.map Term.Set.to_list (Term.Set.subsets (Uf.vars h.eqs)))
  in
  Blist.flatten
    (Blist.map
        (fun ptos ->
          Blist.flatten
            (Blist.map
              (fun preds ->
                Blist.flatten
                  (Blist.map
                      (fun deqs ->
                        Blist.map (fun eqs -> mk eqs deqs ptos preds h.num) all_ufs )
                      all_deqs) )
              all_preds) )
        all_ptos)

(* h' - h *)
let calc_spatial_frame h h' =
  let frame = Ptos.fold (Fun.swap del_pto) h.ptos
    (Tpreds.fold (Fun.swap del_ind) h.inds h') in
  let spat_frame = with_ptos (with_inds empty frame.inds) frame.ptos in
  let rest = Ptos.fold (fun frame_pto h' -> del_pto h' frame_pto) frame.ptos h' in
  let rest = Tpreds.fold (fun frame_pred h'-> del_ind h' frame_pred) frame.inds rest in
  (spat_frame, rest)