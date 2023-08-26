open Lib
open Generic

module SH = Heap

exception Not_symheap = Form.Not_symheap
exception Not_symheap_sum = Form.Not_symheap_sum


module Proof = Proof.Make (Seq)
module Rule = Proofrule.Make (Seq)
module Seqtactics = Seqtactics.Make (Seq)

type t_lemma_level = NO_LEMMAS | ONLY_WITH_PREDICATES | NON_EMPTY | ANY

let lemma_equal lemma lemma' =
  match (lemma, lemma') with
  | NO_LEMMAS, NO_LEMMAS
   |ONLY_WITH_PREDICATES, ONLY_WITH_PREDICATES
   |NON_EMPTY, NON_EMPTY
   |ANY, ANY ->
      true
  | _, _ -> false

let lemma_level = ref ONLY_WITH_PREDICATES

let set_lemma_level level =
  lemma_level :=
    match level with
    | 0 -> NO_LEMMAS
    | 1 -> ONLY_WITH_PREDICATES
    | 2 -> NON_EMPTY
    | 3 -> ANY
    | _ -> raise (Arg.Bad "Unrecognised value for lemma application level")

let lemma_option_descr_str ?(line_prefix = "\t") () =
  let default_str level =
    if lemma_equal !lemma_level level then " (default)" else ""
  in
  line_prefix ^ "0 -- do not attempt to apply any lemmas"
  ^ default_str NO_LEMMAS ^ "\n" ^ line_prefix
  ^ "1 -- only apply lemmas containing predicate instances"
  ^ default_str ONLY_WITH_PREDICATES
  ^ "\n" ^ line_prefix
  ^ "2 -- only apply lemmas with non-empty spatial components"
  ^ default_str NON_EMPTY ^ "\n" ^ line_prefix
  ^ "3 -- attempt all applicable lemmas" ^ default_str ANY

(* TODO: Construct extra rule applications for the case that we need to do    *)
(*       some alpha-renaming, existential introduction or splitting of        *)
(*       existentials (i.e. when the right-hand side is not simply subsumed   *)
(*       the left-hand side). *)
let id_axiom =
  Rule.mk_axiom (fun (((cs, hss), (cs', hss')) as seq) ->
      let constraint_tags = Seq.tags seq in
      let cs = Ord_constraints.close cs in
      Option.map
        (fun _ -> "Id")
        (Unify.Unidirectional.realize
           (Unify.Unidirectional.unify_tag_constraints
              ~update_check:Unify.Unidirectional.modulo_entl cs' cs
              (Unify.Unidirectional.mk_verifier (fun theta ->
                   (not (Blist.is_empty hss'))
                   && Blist.for_all
                        (fun hs -> 
                          (Blist.exists
                            (fun hs' -> 
                              Option.is_some (Heapsum.classical_unify
                                ~update_check:Unify.Unidirectional.modulo_entl constraint_tags hs' hs
                                Unification.trivial_continuation theta)  
                            )
                            hss'))
                        hss)))))

let preddefs = ref Defs.empty

let ex_falso_axiom =
  Rule.mk_axiom (fun (l, _) ->
      Option.mk
        (Form.inconsistent l (*|| not (Basepair.form_sat !preddefs l)*))
        "Ex Falso" )

(* break LHS disjunctions *)
let lhs_disj_to_symheaps =
  Rule.mk_infrule (fun ((cs, hss), r) ->
      match hss with
      | [] | [_] -> []
      | _ ->
          [ ( Blist.map
                (fun hs -> (((cs, [hs]), r), Heapsum.tag_pairs hs, Tagpairs.empty))
                hss
            , "L. Or" ) ] )

(* break RHS disjunctions *)
let rhs_disj_to_symheaps_rl (((_, hss) as l), ((_, hss') as r)) =
  match (hss', hss) with
  | [], _ | [_], _ | _, [] | _, _ :: _ :: _ -> []
  | _ ->
      Blist.map
        (fun hs ->
          ( [ ( (l, Form.with_heapsums r [hs])
              , Form.tag_pairs l
              , Tagpairs.empty ) ]
          , "R. Or" ) )
        hss'

let rhs_disj_to_symheaps = Rule.mk_infrule rhs_disj_to_symheaps_rl

(* Left Instantiation Rules *)

let lhs_instantiate_ex_tags (l, r) =
  let lhs_tags = Form.tags l in
  let exs, univs = Tags.partition Tags.is_exist_var lhs_tags in
  if Tags.is_empty exs then []
  else
    let rhs_tags = Form.tags r in
    let subst = Tagpairs.mk_free_subst (Tags.union lhs_tags rhs_tags) exs in
    [ ( [ ( (Form.subst_tags subst l, r)
          , Tagpairs.union subst (Tagpairs.mk univs)
          , Tagpairs.empty ) ]
      , "Inst. LHS Tags" ) ]

let lhs_instantiate_ex_vars ((l, r) as seq) =
  try
    let (_, hs), (_, hs') = Seq.dest_sum seq in
    let ex_vars = Term.Set.filter Term.is_exist_var (Heapsum.vars hs) in
    if Term.Set.is_empty ex_vars then []
    else
      [ ( [ ( (Form.with_heapsums l [Heapsum.univ (Heapsum.vars hs') hs], r)
            , Form.tag_pairs l
            , Tagpairs.empty ) ]
        , "Inst. LHS Vars" ) ]
  with Not_symheap_sum -> []

let lhs_instantiation_rules = [lhs_instantiate_ex_tags; lhs_instantiate_ex_vars]

let lhs_instantiate_seq =
  Seqtactics.relabel "LHS Inst."
    (Seqtactics.repeat (Seqtactics.first lhs_instantiation_rules))

let lhs_instantiate = Rule.mk_infrule lhs_instantiate_seq

(* simplification rules *)

(* substitute one equality from LHS into sequent *)
(* this equality must appear in all summands in LHS*)
(* for (x,y) substitute y over x as x<y *)
(* this means representatives of eq classes are the max elems *)
let eq_subst_rule ((lhs, rhs) as seq) =
  try
    let (_, ls), (_, rs) = Seq.dest_sum seq in
    match ls with
      | [] -> []
      | l1 :: ls2 -> 
        let leqs1 = Uf.bindings l1.SH.eqs in (*searching only first summand suffices*)
        let leqs1 = Blist.filter (fun leq -> Blist.for_all (fun h ->
          Blist.mem leq (Uf.bindings h.SH.eqs)
          || Blist.mem (Pair.swap leq) (Uf.bindings h.SH.eqs)
        )ls2) leqs1 in
        let ((x, y) as p) =
          Blist.find
            (fun p' -> not (Pair.either (Pair.map Term.is_exist_var p')))
            leqs1
        in
        let ls' = Blist.foldr (
          fun l list ->
            let leqs = Uf.bindings l.SH.eqs in
            let leqs = Blist.filter (fun q -> q <> p && Pair.swap q <> p) leqs in
            let l' = SH.with_eqs l (Uf.of_list leqs) in
            l' :: list
        ) ls [] in
        let x, y = if Term.is_var x then p else (y, x) in
        let theta = Subst.singleton x y in
        let ls', rs' = Pair.map (Heapsum.subst theta) (ls', rs) in
        [ ( [ ( (Form.with_heapsums lhs [ls'], Form.with_heapsums rhs [rs'])
              , Form.tag_pairs lhs
              , (* OK since we didn't modify any tags *)
                Tagpairs.empty ) ]
          , "" ) ]
  with
  | Not_symheap_sum | Not_found -> []

(* substitute one equality in RHS involving an existential var *)
let eq_ex_subst_rule ((lhs, rhs) as seq) =
  try
    let _, (_, rs) = Seq.dest_sum seq in
    let rs' =
      Blist.find_map
        (fun h -> 
          let reqs = Uf.bindings h.SH.eqs in
          let p =
            Blist.find_opt
              (fun vs -> Pair.either (Pair.map Term.is_exist_var vs))
              reqs
          in
          match p with
            | None -> None
            | Some ((x,y) as p) ->
              let reqs = Blist.filter (fun q -> q <> p) reqs in
              let r = SH.with_eqs h (Uf.of_list reqs) in
              let theta =
                if Term.is_exist_var x then Subst.singleton x y
                else Subst.singleton y x
              in
              let r' = Heap.subst theta r in
              Some (Blist.map (fun r -> if r == h then r' else r) rs)
        )
        rs
    in
    match rs' with
      | None -> []
      | Some rs' ->
        [ ( [ ( (lhs, Form.with_heapsums rhs [rs'])
              , Form.tag_pairs lhs
              , Tagpairs.empty ) ]
          , "" ) ]
  with Not_symheap_sum -> []

(* remove all RHS eqs that can be discharged *)
let eq_simplify ((lhs, rhs) as seq) =
  try
    let (_, ls), (_, rs) = Seq.dest_sum seq in
    let rs' = Blist.map (fun r ->
      let disch, reqs =
        Blist.partition
          (fun (x, y) ->
            (not (Pair.either (Pair.map Term.is_exist_var (x, y))))
            && Heapsum.equates ls x y )
          (Uf.bindings r.SH.eqs) in
      if Blist.is_empty disch then r
      else SH.with_eqs r (Uf.of_list reqs)
    ) rs in
    if rs' = rs then []
    else
      [ ( [ ( (lhs, Form.with_heapsums rhs [rs'])
            , Form.tag_pairs lhs
            , Tagpairs.empty ) ]
        , "" ) ]
  with Not_symheap_sum -> []

(* remove all RHS deqs that can be discharged *)
let deq_simplify ((lhs, rhs) as seq) =
  try
    let (_, ls), (_, rs) = Seq.dest_sum seq in
    let rs' = Blist.map (fun r ->
      let disch, rdeqs =
        Deqs.partition
          (fun (x, y) ->
            (not (Pair.either (Pair.map Term.is_exist_var (x, y))))
            && Heapsum.disequates ls x y )
          r.SH.deqs in
      if Deqs.is_empty disch then r
      else SH.with_deqs r rdeqs
    ) rs in
    if rs' = rs then []
    else
      [ ( [ ( (lhs, Form.with_heapsums rhs [rs'])
            , Form.tag_pairs lhs
            , Tagpairs.empty ) ]
        , "" ) ]
  with Not_symheap_sum -> []

(* Remove all RHS constraints that can be discharged *)
let constraint_simplify ((lhs, rhs) as seq) =
  try
    let (cs, _), (cs', _) = Seq.dest_sum seq in
    let cs = Ord_constraints.close cs in
    let discharged, remaining =
      Ord_constraints.partition
        (Fun.disj
           (fun c -> Ord_constraints.Elt.valid c)
           (fun c ->
             Tags.for_all Tags.is_free_var (Ord_constraints.Elt.tags c)
             && Ord_constraints.mem c cs ))
        cs'
    in
    if Ord_constraints.is_empty discharged then []
    else
      [ ( [ ( (lhs, Form.with_constraints rhs remaining)
            , Form.tag_pairs lhs
            , Tagpairs.empty ) ]
        , "" ) ]
  with Not_symheap_sum -> []

let norm seq =
  let seq' = Seq.norm seq in
  if Seq.equal seq seq' then []
  else [([(seq', Seq.tag_pairs seq', Tagpairs.empty)], "")]

let simplify_rules =
  [ eq_subst_rule
  ; eq_ex_subst_rule
  ; eq_simplify
  ; deq_simplify
  ; constraint_simplify
  ; norm ]

let simplify_seq =
  Seqtactics.relabel "Simplify"
    (Seqtactics.repeat (Seqtactics.first simplify_rules))

let simplify = Rule.mk_infrule simplify_seq

let wrap r = 
  Rule.mk_infrule (Seqtactics.compose r (Seqtactics.attempt simplify_seq))

(* do the following transformation for the first x such that *)
(* x->y * A |- x->z * B     if     A |- y=z * B *)
(*When x->y/x->z occurs in every summand*)
let pto_intro_rule =
  let rl seq =
    try
      let (cs, ls), (cs', rs) = Seq.dest_sum seq in
      match (ls, rs) with
       | (_, []) | ([], _) -> []
       | (l1 :: lstail, r1 :: rstail) ->
        let (lys, ((rx, rys) as pr)) =
          Ptos.fold
            (fun ((x, ys) as p) ((lysres, (rxres, rysres)) as res) ->
              if not (Blist.is_empty lysres) then res
              else if not (Blist.for_all (fun r -> Ptos.mem p r.SH.ptos) rstail) then res
              else
                let pl = Blist.find_opt 
                  (fun ((lx', lys') as p') -> 
                    lx' = x
                    && Blist.for_all (fun l -> Ptos.mem p' l.SH.ptos) lstail
                    && Blist.for_all (fun ly -> not (Term.is_exist_var ly)) lys' (*avoid scope jumping*)
                  ) (Ptos.to_list l1.SH.ptos) in
                match pl with
                  | None -> res
                  | Some (lx, lys) -> (lys, (x, ys)) 
            ) r1.SH.ptos ([], (Term.of_string "a", []))
        in
        if Blist.is_empty lys then []
        else
          (* take care to remove only the 1st match *)
          let ls' = Blist.map (fun l -> SH.del_pto l (rx, lys)) ls in
          let rs' = Blist.map (fun r -> 
            let r' = SH.del_pto r pr in
            SH.with_eqs r' (Uf.union r'.SH.eqs (Uf.of_list (Blist.combine rys lys)))
          ) rs in
          [ ( [(((cs, [ls']), (cs', [rs'])), Heapsum.tag_pairs ls, Tagpairs.empty)]
            , "Pto Intro" ) ]
    with
    | Not_symheap_sum | Not_found | Invalid_argument _ -> []
  in
  wrap rl
 
(* do the following transformation for the first P, (x_1,...,x_n) such that *)
(*   P[a](x_1, ..., x_n) * A |- P[b](x_1, ..., x_n) * B    if  A |- B[a/b]  *)
(* with [a] a universal tag and either [b] = [a] or [b] existential         *)
(* P has to appear in all summands and either both sides are one heap, or RHS is one heap, or P is domain-exact*)
let pred_intro_rule defs =
  let rl ((l, r) as seq) =
    try
      let (_, hs), (_, hs') = Seq.dest_sum seq in
      match (hs, hs') with
        | ([], _) | (_, []) -> []
        | (h :: hs, h' :: hs') ->
          let must_be_domain_exact = not (Blist.is_empty hs') in
          let linds, rinds = Pair.map Tpreds.elements (h.SH.inds, h'.SH.inds) in
          let linds = Blist.filter (fun lind -> 
            Blist.for_all (fun h -> Tpreds.mem lind h.SH.inds) hs
            && (not must_be_domain_exact || Form.is_domain_exact (Defs.get_def_forms defs) (Form.mk_heap (Heap.mk_ind lind)))
          ) linds in
          let rinds = Blist.filter (fun rind ->
            Blist.for_all (fun h' -> Tpreds.mem rind h'.SH.inds) hs'
            && (not must_be_domain_exact || Form.is_domain_exact (Defs.get_def_forms defs) (Form.mk_heap (Heap.mk_ind rind)))  
          ) rinds in
          let cp = Blist.cartesian_product linds rinds in
          let matches ((t, (id, vs)), (t', (id', vs'))) =
            Predsym.equal id id'
            && Blist.for_all (Fun.neg Term.is_exist_var) vs
            && Blist.for_all (Fun.neg Term.is_exist_var) vs'
            && Tags.is_free_var t
            && (Tags.is_exist_var t' || Tags.Elt.equal t t')
          in
          let combine_eqs h h' =
            let ts, ts' = Pair.map Heap.vars (h, h') in
            let exs = Term.Set.filter Term.is_exist_var ts in
            let h_eqs =
              if Term.Set.is_empty exs then h.SH.eqs
              else
                let theta =
                  Subst.mk_free_subst (Term.Set.union ts ts') exs
                in
                Uf.subst theta h.SH.eqs
            in
            let combined_eqs = Uf.union h_eqs h'.SH.eqs in
            Uf.equates combined_eqs
          in
          let hs = [h] @ hs in
          let hs' = [h'] @ hs' in
          let p, q =
            Option.dest
              (Blist.find (fun (((t, (id, vs)), (t', (id', vs'))) as cp) ->
                matches cp && Blist.for_all2 (fun v v' ->
                  let heap_product = Blist.cartesian_product hs hs' in
                  Blist.for_all (fun (h, h') -> (combine_eqs h h') v v') heap_product)
                vs vs')
              cp)
              Fun.id
              (Blist.find_opt (fun (((t, (id, vs)), (t', (id', vs'))) as cp) ->
                matches cp && Blist.for_all2 (Heap.equates h) vs vs')
              cp)
          in
          let hs = Blist.map (fun h -> SH.del_ind h p) hs in
          let hs' = Blist.map (fun h' -> SH.del_ind h' q) hs' in
          let t, t' = Pair.map Tpred.tag (p, q) in
          let subst = Tagpairs.singleton (t', t) in
          let rl_name =
            if Tags.Elt.equal t t' then "Pred Intro" else "Tag.Inst+Pred.Intro"
          in
          [ ( [ ( ( Form.with_heapsums l [hs]
                  , Form.subst_tags subst (Form.with_heapsums r [hs']) )
                , Heapsum.tag_pairs hs
                , Tagpairs.empty ) ]
            , rl_name ) ]
    with
    | Not_symheap_sum | Not_found -> []
  in
  wrap rl

(* x->ys * A |- e->zs * B if  A |- ys=zs * B[x/e] where e existential *)
(* and at least one var in ys,zs is the same *)
(* x->ys, e->zs, ys=zs have to appear in all summands on the respective side*)
(* multiple applications possible *)
let instantiate_pto =
  let rl seq =
    try
      let (cs, ls), (cs', rs) = Seq.dest_sum seq in
      match (ls, rs) with
        | ([], _) | (_, []) -> []
        | (l :: ls, r :: rs) ->
          let lptos, rptos = Pair.map Ptos.elements (l.SH.ptos, r.SH.ptos) in
          let eptos = Blist.filter (fun (x, _) -> Term.is_exist_var x) rptos in
          let lptos = Blist.filter (fun p -> Blist.for_all (fun l -> Ptos.mem p l.SH.ptos) ls) lptos in
          let eptos = Blist.filter (fun p -> Blist.for_all (fun r -> Ptos.mem p r.SH.ptos) rs) eptos in
          let match_ls xs ys =
            try
              (* avoid scope jumping *)
              (not (Blist.exists Term.is_exist_var xs))
              && Blist.exists2 (fun x y -> Heapsum.equates ([l] @ ls) x y) xs ys
            with Invalid_argument _ -> false
          in
          let cp = Blist.cartesian_product eptos lptos in
          let cp = Blist.filter (fun ((_, zs), (_, ys)) -> match_ls ys zs) cp in
          let do_instantiation (((x, ys) as p), ((w, zs) as q)) =
            let ls' = Blist.map (fun l -> SH.del_pto l q ) ([l] @ ls) in
            let rs' = Blist.map (fun r -> SH.del_pto r p ) ([r] @ rs) in
            let rs' = Blist.map
              (fun r' ->
                SH.with_eqs r'
                  (Uf.union r'.SH.eqs
                    (Uf.of_list ((x, w) :: Blist.combine ys zs)))
              ) rs' in
            ( [(((cs, [ls']), (cs', [rs'])), Heapsum.tag_pairs ([l] @ ls), Tagpairs.empty)]
            , "Inst Pto" )
          in
          Blist.map do_instantiation cp
    with
    | Not_symheap_sum | Invalid_argument _ -> []
  in
  wrap rl

(* ([a] <(=) [b], ...) : F |- ([c] <(=) [d], ...) : G            *)
(*   if ([a] <(=) [b], ...) : F |- theta((...) : G)              *)
(* where [a] and [b] universal and either :                      *)
(*   - [a] = [c] and [d] existential with theta = ([d], [b]); or *)
(*   - [b] = [d] and [c] existential with theta = ([c], [a])     *)
let constraint_match_tag_instantiate =
  let rl (((cs, _) as l), ((cs', _) as r)) =
    let do_instantiation c =
      let singleton = Ord_constraints.singleton c in
      let tags = Ord_constraints.tags singleton in
      if Tags.for_all Tags.is_exist_var tags then None
      else
        let unifier =
          Ord_constraints.unify
            ~update_check:
              (Ord_constraints.mk_update_check
                 (Fun.disj
                    (fun (_, (t, t')) ->
                      Tags.is_free_var t && Tags.Elt.equal t t' )
                    (fun (_, (t, t')) ->
                      Tags.is_exist_var t && Tags.is_free_var t' )))
        in
        let subs =
          Unification.backtrack unifier singleton cs
            Unification.trivial_continuation Tagpairs.empty
        in
        if Blist.is_empty subs then None
        else
          let ruleapps =
            Blist.map
              (fun theta ->
                ( [ ( (l, Form.subst_tags theta r)
                    , Form.tag_pairs l
                    , Tagpairs.empty ) ]
                , "Inst.Tag (Match)" ) )
              subs
          in
          Option.some ruleapps
    in
    Option.dest [] Fun.id (Ord_constraints.find_map do_instantiation cs')
  in
  wrap rl

(* F |- ([b'] <= [a] ...) : G  if  F |- theta((...) : G)           *)
(*   where [a] universal, [b'] existential and theta = ([b'], [a]) *)
let upper_bound_tag_instantiate =
  let rl (l, ((cs, _) as r)) =
    let do_instantiation t =
      let ts = Ord_constraints.upper_bounds t cs in
      let ts = Tags.filter Tags.is_free_var ts in
      if Tags.is_empty ts then None
      else
        let ruleapps =
          Tags.map_to_list
            (fun t' ->
              let theta = Tagpairs.singleton (t, t') in
              ( [ ( (l, Form.subst_tags theta r)
                  , Form.tag_pairs l
                  , Tagpairs.empty ) ]
              , "Inst.Tag (Sel.UBound)" ) )
            ts
        in
        Some ruleapps
    in
    let ts = Tags.filter Tags.is_exist_var (Ord_constraints.tags cs) in
    let ruleapps = Tags.find_map do_instantiation ts in
    Option.dest [] Fun.id ruleapps
  in
  wrap rl

(* Lower and Upper Bound Constraint Introduction - do one of:               *)
(*   A |- b' <= a_1, ..., b' <= a_n : B  if  A |- B                         *)
(*   A |- a_1 <= b', ..., a_n <= b' : B  if  A |- B                         *)
(*   A |- a_1 < b', ..., a_n < b' : B    if  A |- B                         *)
(* where b' is a fresh existential tag not occurring in B and a_1, ..., a_n *)
(* can be any tags *)
let bounds_intro_rl ((l, r) as seq) =
  try
    let _, (cs, hs) = Seq.dest_sum seq in
    let f (cs, descr) =
      [ ( [ ( (l, Form.with_constraints r cs)
            , Form.tag_pairs l
            , Tagpairs.empty ) ]
        , descr ^ " Intro" ) ]
    in
    let result = Ord_constraints.remove_schema cs (Heapsum.tags hs) in
    Option.dest [] f result
  with Not_symheap_sum -> []

let bounds_intro = Rule.mk_infrule bounds_intro_rl

let ruf_rl defs seq =
  try
    let (cs, ls), (cs', rs) = Seq.dest_sum seq in
    let seq_vars = Seq.vars seq in
    let seq_tags = Seq.tags seq in
    let right_unfold (r, ((tag, (ident, _)) as p)) =
      if not (Defs.mem ident defs) then []
      else
        let r' =  Heap.with_inds r (Tpreds.del_first (fun ind -> ind == p) r.SH.inds) in (*TODO check domain-exact? also lUnfold?*)
        let cases = Defs.unfold (seq_vars, seq_tags) p defs in
        let do_case f =
          let cs' =
            Ord_constraints.union cs'
              (Ord_constraints.generate ~avoid:seq_tags ~augment:false tag (Heapsum.tags f))
          in
          let r' = Heapsum.star [r'] f in
          let tps =
            Tagpairs.union (Heapsum.tag_pairs ls) (Ord_constraints.tag_pairs cs)
          in
          let rs' = Blist.flatten (Blist.map (fun r'' -> if r'' == r then r' else [r'']) rs) in
          (*print_endline ("hiiii " ^ "R': " ^ Heapsum.to_string r' ^ " | Res: " ^ Form.to_string (cs', [rs']));*)
          ( [(((cs, [ls]), (cs', [rs'])), tps, Tagpairs.empty)]
          , Predsym.to_string ident ^ " R.Unf." )
        in
        Blist.map do_case cases
    in
    let heap_preds = 
      Blist.foldl ( fun list r ->
        list @ Blist.map (fun pred -> (r, pred)) (Tpreds.to_list r.SH.inds)
      ) [] rs in
    let res = Blist.flatten (Blist.map right_unfold heap_preds) in
    (*print_endline (Blist.to_string " || " (fun 
      (rs, _) -> match rs with
      | ((_, (cs, rs::rss)), _, _) :: _ -> Heapsum.to_string rs
      | _ -> ""
    ) res);*)
    res
  with Not_symheap_sum -> []

let ruf defs = wrap (ruf_rl defs)

let luf defs =
  let rl seq =
    try
      let (cs, ls), (cs', rs) = Seq.dest_sum seq in
      let seq_vars = Seq.vars seq in
      let seq_tags = Seq.tags seq in
      let left_unfold (l, ((tag, (ident, _)) as p)) =
        if not (Defs.mem ident defs) then None
        else
          let l' = SH.with_inds l (Tpreds.del_first (fun pred -> pred == p) l.SH.inds) in
          let cases = Defs.unfold (seq_vars, seq_tags) p defs in
          let do_case f =
            let new_cs =
              Ord_constraints.union cs
                (Ord_constraints.generate ~avoid:seq_tags tag (Heapsum.tags f))
            in
            let cclosure = Ord_constraints.close new_cs in
            let vts, pts =
              let collect tps =
                Tagpairs.map Pair.swap
                  (Tagpairs.filter (fun (_, t) -> Tags.mem t seq_tags) tps)
              in
              Pair.map collect
                ( Ord_constraints.all_pairs cclosure
                , Ord_constraints.prog_pairs cclosure )
            in
            let vts = Tagpairs.union vts (Tagpairs.mk (Heapsum.tags ls)) in 
            let l' = Heapsum.star [l'] f in
            let ls' = Blist.flatten (Blist.map (fun l'' -> if l'' == l then l' else [l'']) ls) in
            (((new_cs, [ls']), (cs', [rs])), vts, pts)(*TODO === ls' (I believe so)?*)
          in
          Some (Blist.map do_case cases, Predsym.to_string ident ^ " L.Unf.")
      in
      let heap_preds =
        Blist.foldl (fun list l ->
          list @ Blist.map (fun pred -> (l, pred)) (Tpreds.to_list l.SH.inds)
        ) [] ls in
      Option.list_get (Blist.map left_unfold heap_preds)
    with Not_symheap_sum -> []
  in
  wrap (Seqtactics.compose rl (Seqtactics.attempt lhs_instantiate_seq))

let mapping_str mapping =
  "(" ^ Blist.to_string ")(" (fun map -> string_of_int (fst map) ^ "," ^ string_of_int (snd map)) mapping ^ ")"

(* seq' = (l',r') *)
(* ------------   *)
(* seq = (l ,r )  *)
(* where there exists a substitution theta such that *)
(* seq'[theta] entails seq by subsumption    *)
(* that is whenever *)
(* l subsumes l'[theta] *)
(* and *)
(* r'[theta] subsumes r *)
let matches ((lhs, rhs) as seq) =
  try
    let (lcs, ls), (rcs, rs) = Seq.dest_sum seq in
    fun ((lhs', rhs') as seq') ->
      try
        let (lcs', ls'), (rcs', rs') = Seq.dest_sum seq' in
        if Blist.for_all (fun l' -> Tpreds.is_empty l'.SH.inds) ls' then []
        else
          let l_c_tags = Tags.union (Ord_constraints.tags lcs') (Ord_constraints.tags lcs) in
          let lcs = Ord_constraints.close lcs in (*TODO only those constraints?*)
          let lhs_check =
            Fun.disj Unify.Unidirectional.is_substitution
              Unify.Unidirectional.modulo_entl
          in
          Unify.Unidirectional.realize
            (Unification.backtrack
               (Heapsum.unify_partial ~update_check:lhs_check l_c_tags)
               ls' ls
               (Unify.Unidirectional.unify_tag_constraints ~inverse:false
                  ~update_check:lhs_check lcs' lcs
                  (fun ((trm_subst, tag_subst, mappings_l) as state) ->
                    let () =
                      debug (fun _ ->
                          "Checking results of unification for LHS:\n\t"
                          ^ "Term subst: "
                          ^ Term.Map.to_string Term.to_string trm_subst
                          ^ ", " ^ "Tag subst: "
                          ^ Tagpairs.to_string tag_subst
                          ^ "\n\tMappingL: " ^ mapping_str mappings_l
                          ^ "\n\tTargL: " ^ Form.to_string lhs' ^ "\n\tSrcL: "
                          ^ Form.to_string lhs )
                    in
                    let lhs = Form.with_constraints lhs lcs in
                    let lhs' =
                      Form.subst_tags tag_subst
                        (Form.subst trm_subst lhs')
                    in
                    let ((lhs', lhs), (lhs_rest', lhs_rest)) = Seq.partition_summands (lhs', lhs) mappings_l in
                    let _, ls' = Form.dest_sum lhs' in
                    let _, ls = Form.dest_sum lhs in
                    (*let ls_rest' = try
                      let _, ls_rest' = Form.dest_sum lhs_rest' in
                      ls_rest'
                    with Not_symheap_sum -> [] in*)
                    assert (Form.subsumed ~total:false lhs' lhs) ;
                    if not (Heapsum.subsumed ls' ls) then (*TODO more efficient than always calling subsumed?*)
                      if lemma_equal !lemma_level NO_LEMMAS then None
                      else if
                        lemma_equal !lemma_level ONLY_WITH_PREDICATES
                        && Blist.for_all (fun l' -> Tpreds.is_empty l'.SH.inds) ls'
                      then None
                      else if
                        lemma_equal !lemma_level NON_EMPTY
                        && Blist.for_all (fun l' -> Tpreds.is_empty l'.SH.inds) ls'
                        && Blist.for_all (fun l' -> Ptos.is_empty l'.SH.ptos) ls'
                      then None
                      else Option.some state
                    else
                      let () =
                        debug (fun _ -> "Continuing with unification of RHS")
                      in
                      let trm_theta, _ = Subst.partition trm_subst in
                      let tag_theta, _ = Tagpairs.partition_subst tag_subst in
                      let r_c_tags = Tags.union (Ord_constraints.tags rcs') (Ord_constraints.tags rcs) in
                      let rcs' = Ord_constraints.close rcs' in
                      let rhs_check =
                        Fun.conj
                          (Unify.Bidirectional.updchk_inj_left
                             Unify.Unidirectional.modulo_entl)
                          (Unify.Bidirectional.updchk_inj_right
                             Unify.Unidirectional.is_substitution)
                      in
                      let bisubst =
                        (Heapsum.classical_biunify ~update_check:rhs_check r_c_tags rs rs'
                           (Unify.Bidirectional.unify_tag_constraints
                              ~update_check:rhs_check rcs rcs'
                              (fun ( ( (trm_subst, tag_subst, mappings_r)
                                     , (trm_subst', tag_subst', mappings_r') ) as state )
                              ->
                                let () =
                                  debug (fun _ ->
                                      "Checking results of biunification for \
                                       RHS:\n\
                                       \t" ^ "Term subst': "
                                      ^ Term.Map.to_string Term.to_string
                                          trm_subst'
                                      ^ ", " ^ "Tag subst': "
                                      ^ Tagpairs.to_string tag_subst'
                                      ^ "\n\t" ^ "Term subst: "
                                      ^ Term.Map.to_string Term.to_string
                                          trm_subst
                                      ^ ", " ^ "Tag subst: "
                                      ^ Tagpairs.to_string tag_subst
                                      ^ "\n\tMappingR: " ^ mapping_str mappings_r
                                      ^ "\n\tSrcR: " ^ Form.to_string rhs
                                      ^ "\n\tTargR: " ^ Form.to_string rhs' )
                                in
                                let rhs' =
                                  Form.with_constraints rhs' rcs'
                                in
                                let rhs' =
                                  Form.subst_tags tag_subst'
                                    (Form.subst trm_subst' rhs')
                                in
                                let rhs =
                                  Form.subst_tags tag_subst
                                    (Form.subst trm_subst rhs)
                                in
                                let (rhs, rhs'), _ = Seq.partition_summands (rhs, rhs') mappings_r in
                                assert (Form.subsumed rhs rhs') ;
                                Option.some state )))
                          ( Unify.Unidirectional.empty_state
                          , (trm_theta, tag_theta, []) )
                      in
                      Option.map
                        (fun (_, (trm_subst', tag_subst', mappings_r)) ->
                          let trm_subst', _ = Subst.partition trm_subst' in
                          let tag_subst', _ =
                            Tagpairs.partition_subst tag_subst'
                          in
                          ( Term.Map.union trm_subst trm_subst'
                          , Tagpairs.union tag_subst tag_subst',
                          mappings_l @ [(-2, -2)] @ mappings_r))
                        bisubst )))
      with Not_symheap_sum -> []
  with Not_symheap_sum -> fun _ -> []
   
(*    seq'     *)
(* ----------  *)
(* seq'[theta] *)
(* where seq'[theta] = seq *)
let subst_rule (theta, tps) ((l', _) as seq') ((l, _) as seq) =
  if Seq.equal seq (Seq.subst_tags tps (Seq.subst theta seq')) then
    let tagpairs =
      Tagpairs.filter
        (fun (t, t') ->
          Tags.mem t' (Form.tags l') && Tags.mem t (Form.tags l) )
        (Tagpairs.reflect tps)
    in
    let unmapped = Tags.diff (Form.tags l) (Tagpairs.projectl tagpairs) in
    let remaining = Tags.inter unmapped (Form.tags l') in
    let tagpairs = Tagpairs.union tagpairs (Tagpairs.mk remaining) in
    [([(seq', tagpairs, Tagpairs.empty)], "Subst")]
  else
    let () =
      debug (fun _ -> "Unsuccessfully tried to apply substitution rule!")
    in
    []
    
(*   F |- G * Pi'  *)
(* --------------- *)
(*   Pi * F |- G   *)
(* where seq' = F |- G * Pi' and seq = Pi * F |- G *)
let weaken seq' seq =
  (* let () = debug (fun _ -> "Trying to apply weakening:") in *)
  (* let () = debug (fun _ -> Seq.to_string seq') in        *)
  (* let () = debug (fun _ -> Seq.to_string seq) in         *)
  if Seq.subsumed seq seq' then
    [([(seq', Seq.tag_pairs seq', Tagpairs.empty)], "Weaken")]
  else
    let () =
      debug (fun _ -> "Unsuccessfully tried to apply weakening rule!")
    in
    let () = debug (fun _ -> Seq.to_string seq') in
    let () = debug (fun _ -> Seq.to_string seq) in
    []
   
let left_transform_rule ((lhs', rhs') as seq') (lhs, rhs) =
  try
    let lhs_cs', lhs_hs' = Form.dest_sum lhs' in
    let lhs_cs, lhs_hs = Form.dest_sum lhs in
    let constraint_tags = Tags.union (Ord_constraints.tags lhs_cs') (Ord_constraints.tags lhs_cs) in
    if Form.equal rhs' rhs then
      let transform =
        Unify.Unidirectional.realize
          ((Heapsum.classical_unify
              ~update_check:Unify.Unidirectional.modulo_entl constraint_tags lhs_hs' lhs_hs)
              (Unify.Unidirectional.unify_tag_constraints
                ~update_check:Unify.Unidirectional.modulo_entl lhs_cs'
                lhs_cs Unification.trivial_continuation))
      in
      if Option.is_some transform then
        let _, tps, _ = Option.get transform in
        let tps = Tagpairs.reflect tps in
        [([(seq', tps, Tagpairs.empty)], "L.Trans.Ex")]
      else
        let () =
          debug (fun _ ->
              "Unsuccessfully tried to apply left transformation rule!" )
        in
        []
    else
      let () =
        debug (fun _ ->
            "Unsuccessfully tried to apply left transformation rule - \
              right-hand sides not equal!" )
      in
      []
  with Not_symheap_sum ->
    let () =
      debug (fun _ ->
          "Unsuccessfully tried to apply left transformation rule - one \
            left-hand side not a symbolic heap!" )
    in
    []
  
let right_transform_rule ((lhs', rhs') as seq') (lhs, rhs) =
  try
    let rhs_cs', rhs_hs' = Form.dest_sum rhs' in
    let rhs_cs, rhs_hs = Form.dest_sum rhs in
    let constraint_tags = Tags.union (Ord_constraints.tags rhs_cs') (Ord_constraints.tags rhs_cs) in
    if Form.equal lhs' lhs then
      let transform =
        Unify.Unidirectional.realize
          ((Heapsum.classical_unify
              ~update_check:Unify.Unidirectional.modulo_entl constraint_tags rhs_hs rhs_hs')
              (Unify.Unidirectional.unify_tag_constraints
                ~update_check:Unify.Unidirectional.modulo_entl rhs_cs
                rhs_cs' Unification.trivial_continuation))
      in
      if Option.is_some transform then
        [([(seq', Seq.tag_pairs seq', Tagpairs.empty)], "R.Trans.Ex")]
      else
        let () =
          debug (fun _ ->
              "Unsuccessfully tried to apply right transformation rule!" )
        in
        []
    else
      let () =
        debug (fun _ ->
            "Unsuccessfully tried to apply right transformation rule - \
              left-hand sides not equal!" )
      in
      []
  with Not_symheap_sum ->
    let () =
      debug (fun _ ->
          "Unsuccessfully tried to apply right transformation rule - one \
            right-hand side not a symbolic heap!" )
    in
    []

let split_sum_rule ((lhs1', rhs1') as seq1') ((lhs2', rhs2') as seq2') seq = 
  [([(seq1', Seq.tag_pairs seq1', Tagpairs.empty); (seq2', Seq.tag_pairs seq2', Tagpairs.empty)], "Split Sum")]

(**
    Apply lemma to seq lhs'=hs' |- rhs'
    Lemma: ls |- rs
    cont: lhs=hs |- rhs
    
    lemma = unfolding of predicate (apply inverse to h, so:)
    l + h - r = h'

      seq: hs' |- rhs'
    --------------------
      cont: hs |- rhs

    Assume that rs of lemma is only one summand (since right of predicate is only one symbol)
    and do the reverse lemma application for every summand of hs independently
*)
let apply_lemma defs (lemma_seq, ((lhs, rhs) as cont_seq), rest_src_lhs) ((lhs', rhs') as seq) =
  let () =
    debug (fun _ -> "Trying to apply lemma to subgoal: " ^ Seq.to_string seq)
  in
  let (lcs, ls), (rcs, rs) = Seq.dest_sum lemma_seq in
  let cs, hs = Form.dest_sum lhs in
  let cs_add, hs_add = Form.dest_sum rest_src_lhs in
  let true_cont_seq = ((Ord_constraints.union cs cs_add, [hs @ hs_add]), rhs) in
  let () = debug (fun _ -> "Lemma: " ^ Seq.to_string lemma_seq) in
  let () = debug (fun _ -> "Continuation: " ^ Seq.to_string true_cont_seq) in
  assert (Ord_constraints.equal cs (Ord_constraints.union lcs rcs)) ;
  (*assert (Ptos.subset r.SH.ptos h.SH.ptos) ;
  assert (Tpreds.subset r.SH.inds h.SH.inds) ;*)
  (* The separating conjunction of the lemma antecedent and the frame may *)
  (* introduce more disequalities that simply the union *)
  (*assert (Deqs.subset (Deqs.union l.SH.deqs r.SH.deqs) h.SH.deqs) ;
  assert (Uf.subsumed l.SH.eqs h.SH.eqs) ; TODO include again?
  assert (Uf.subsumed r.SH.eqs h.SH.eqs) ;
  assert (
    Uf.subsumed h.SH.eqs
      (Uf.fold (Fun.curry Uf.add) l.SH.eqs r.SH.eqs) ) ;*)
  try
    let cs', hs' = Form.dest_sum lhs' in
    (*let expected =
      Blist.flatten (Blist.map (fun h ->
        let diff = 
          Blist.foldl (fun h r -> Heap.with_ptos
            (Heap.with_inds Heap.empty (Tpreds.diff h.SH.inds r.SH.inds))
            (Ptos.diff h.SH.ptos r.SH.ptos)
          ) h rs in
          (*Since from up to down, the max value of LHS would be lowered if pred not domain exact, it is okay to not do this check*)
          (*if Blist.length ls <= 1 || Tpreds.for_all (fun pred -> 
            Form.is_domain_exact (Defs.get_def_forms defs) (Form.mk_heap (Heap.mk_ind pred))
          ) diff.SH.inds then*)
        Heapsum.star ls [diff]
          (*else [h]*)
      ) hs)
    in*)
    let () = debug (fun _ -> "Constraints match: " ^ (string_of_bool (Ord_constraints.equal lcs cs'))) in
    let () = debug (fun _ -> "RHS match: " ^ (string_of_bool (Form.equal rhs rhs'))) in
    if
      Ord_constraints.equal lcs cs' (*TODO should we check this or not?*)
      (*&& Heapsum.equal hs' expected*)(*This check is not that easy anymore, skip it, should be given by construction*)
      && Form.equal rhs rhs'
    then
      let vts, pts = Seq.get_tracepairs seq cont_seq in
      [ ( [ (lemma_seq, Seq.tag_pairs lemma_seq, Tagpairs.empty)
          ; (true_cont_seq, vts, pts) ]
        , "Lemma.App" ) ]
    else
      let () =
        debug (fun _ ->
            "Unsuccessfully tried to apply lemma - open node does not match \
             expected!" )
      in
      []
  with Not_symheap_sum ->
    let () =
      debug (fun _ ->
          "Unsuccessfully tried to apply lemma - LHS of open node not a \
           symbolic heap!" )
    in
    []

let mk_backlink_rule_seq (trm_subst, tag_subst) ((mapped_src_lhs, mapped_src_rhs) as mapped_src_seq) 
    (((_, rest_src_lss), _) as rest_src_seq) do_split (targ_idx, targ_seq) =
  let ((subst_lhs, subst_rhs) as subst_seq) =
    Seq.subst trm_subst (Seq.subst_tags tag_subst targ_seq)
  in
  let (subst_lhs_cs, subst_lhs_hs), (subst_rhs_cs, subst_rhs_hs) =
    Seq.dest_sum subst_seq
  in
  let (src_lhs_cs, src_lhs_hs), (src_rhs_cs, src_rhs_hs) = Seq.dest_sum mapped_src_seq in
  let src_lhs_cs = Ord_constraints.close src_lhs_cs in
  let subst_rhs_cs = Ord_constraints.close subst_rhs_cs in
  let l_constraint_tags = Tags.union (Ord_constraints.tags subst_lhs_cs) (Ord_constraints.tags src_lhs_cs) in
  let lhs_transform = 
    Unify.Unidirectional.realize
      ((Heapsum.classical_unify
          ~update_check:Unify.Unidirectional.modulo_entl l_constraint_tags subst_lhs_hs
          src_lhs_hs)
         (Unify.Unidirectional.unify_tag_constraints (*Left: theta(Backlink target node) subset of leaf node*)
            ~update_check:Unify.Unidirectional.modulo_entl subst_lhs_cs
            src_lhs_cs Unification.trivial_continuation))
  in
  let r_constraint_tags = Tags.union (Ord_constraints.tags subst_rhs_cs) (Ord_constraints.tags src_rhs_cs) in
  let rhs_transform =
    Unify.Unidirectional.realize
      ((Heapsum.classical_unify
          ~update_check:Unify.Unidirectional.modulo_entl r_constraint_tags src_rhs_hs
          subst_rhs_hs)
         (Unify.Unidirectional.unify_tag_constraints (*Right: Leaf node subset of theta(Backlink target node)*)
            ~update_check:Unify.Unidirectional.modulo_entl src_rhs_cs
            subst_rhs_cs Unification.trivial_continuation))
  in
  let () =
    debug (fun _ ->
        "Checking transform for LHS:\n\t"
        ^ Form.to_string subst_lhs
        ^ "\n\t" ^ Form.to_string mapped_src_lhs )
  in
  assert (Option.is_some lhs_transform) ;
  let () =
    debug (fun _ ->
        "Checking transform for RHS:\n\t"
        ^ Form.to_string subst_rhs
        ^ "\n\t" ^ Form.to_string mapped_src_rhs )
  in
  assert (Option.is_some rhs_transform) ;
  let lhs_trm_transform, lhs_tag_transform, _ = Option.get lhs_transform in
  let rhs_trm_transform, rhs_tag_transform, _ = Option.get rhs_transform in
  let transformed_lhs =
    Form.subst_tags lhs_tag_transform
      (Form.subst lhs_trm_transform subst_lhs)
  in
  let transformed_rhs =
    Form.subst_tags rhs_tag_transform
      (Form.subst rhs_trm_transform mapped_src_rhs)
  in
  let left_transformed_seq = (transformed_lhs, subst_rhs) in
  let right_transformed_seq = (mapped_src_lhs, transformed_rhs) in
  let split_rule = Rule.mk_infrule (split_sum_rule mapped_src_seq rest_src_seq) in
  let backl_seq = Rule.sequence
    [ ( if Seq.equal mapped_src_seq right_transformed_seq then Rule.identity
      else Rule.mk_infrule (right_transform_rule right_transformed_seq) )
    ; ( if Seq.equal right_transformed_seq left_transformed_seq then
        Rule.identity
      else Rule.mk_infrule (weaken left_transformed_seq) )
    ; ( if Seq.equal left_transformed_seq subst_seq then Rule.identity
      else Rule.mk_infrule (left_transform_rule subst_seq) )
    ; ( if Seq.equal subst_seq targ_seq then Rule.identity
      else Rule.mk_infrule (subst_rule (trm_subst, tag_subst) targ_seq) )
    ; Rule.mk_backrule true
        (fun _ _ -> [targ_idx])
        (fun s s' -> [(Seq.tag_pairs s', "Backl")]) ]
  in
  if do_split && Blist.length rest_src_lss > 0 && Blist.length (Blist.nth rest_src_lss 0) > 0 then
    Rule.compose_pairwise split_rule [backl_seq; Rule.identity]
  else
    backl_seq

let mk_lemma_rule_seq (trm_subst, tag_subst, _) (mapped_src_lhs, _)
  ((rest_src_lhs, rest_src_rhs) as rest_src_seq) defs
    (targ_idx, ((lhs, rhs) as targ_seq)) =
  let cs, hs = Form.dest_sum mapped_src_lhs in
  let trm_theta, _ = Subst.partition trm_subst in
  let tag_theta, _ = Tagpairs.partition_subst tag_subst in
  let subst_lhs = Form.subst trm_subst (Form.subst_tags tag_subst lhs) in
  let subst_rhs = Form.subst trm_theta (Form.subst_tags tag_theta rhs) in
  let subst_seq = (subst_lhs, subst_rhs) in
  (* let () = debug (fun _ -> "substituted seq is " ^ (Seq.to_string subst_seq)) in *)
  let subst_cs, subst_hs = Form.dest_sum subst_lhs in
  (* Calculate the frame for each summand matching pair independently (ordering of the sums is consistent to matching) *)
  let (_, frames) = (*h(src_lhs) - subst_h(target_lhs)*)
    Blist.foldl (fun (subst_hs, frames) h ->
      match subst_hs with
        | [] -> ([], frames)
        | subst_h :: subst_hs ->
          let frame = Ptos.fold (Fun.swap Heap.del_pto) subst_h.SH.ptos
            (Tpreds.fold (Fun.swap Heap.del_ind) subst_h.SH.inds h)
          in
          (subst_hs, frames @ [frame])
    ) (subst_hs, []) hs
  in
  let () = debug (fun _ ->
    "src_lhs: " ^ Heapsum.to_string hs
    ^ "\ntarget_lhs: " ^ Heapsum.to_string subst_hs
    ^ "\nframe=src-target: " ^ Heapsum.to_string frames
  ) in
  (* let () = debug (fun _ -> "Calculated frame is " ^ (Heap.to_string frame)) in *)
  (* Alpha-rename any clashing existential variables in the succedent of the lemma *)
  let ctxt_vars =
    Term.Set.union (Heapsum.terms frames) (Form.terms rest_src_rhs)
  in
  let ctxt_tags =
    Tags.union_of_list
      [Heapsum.tags frames; Ord_constraints.tags cs; Form.tags rest_src_rhs]
  in
  let clashed_tags =
    Tags.inter ctxt_tags
      (Tags.filter Tags.is_exist_var (Form.tags subst_rhs))
  in
  let clashed_vars =
    Term.Set.inter ctxt_vars
      (Term.Set.filter Term.is_exist_var (Form.terms subst_rhs))
  in
  let all_tags = Tags.union ctxt_tags (Seq.tags subst_seq) in
  let all_vars = Term.Set.union ctxt_vars (Seq.vars subst_seq) in
  let tag_subst' = Tagpairs.mk_ex_subst all_tags clashed_tags in
  let trm_subst' = Subst.mk_ex_subst all_vars clashed_vars in
  let subst_rhs =
    Form.subst trm_subst' (Form.subst_tags tag_subst' subst_rhs)
  in
  (* Construct the new subgoals *)
  let lemma_seq =
    let (_, subst_hs) = 
      Blist.foldl (fun (subst_hs, reslist) h ->
        match subst_hs with
        | [] -> ([], reslist)
        | subst_h :: subst_hs ->
          let res = Heap.with_eqs (Heap.with_deqs subst_h h.SH.deqs) h.SH.eqs in
          (subst_hs, reslist @ [res])
      ) (subst_hs, []) hs
    in
    ((cs, [subst_hs]), subst_rhs)
  in
  (* let () = debug (fun _ -> (Heap.to_string subst_h') ^ " * " ^ (Heap.to_string frame) ^ " = " ^ (Heap.to_string (Heap.star subst_h' frame))) in *)
  (*TODO cont_seq STAR rule???*)
  let cont_seq = (Form.star (cs, [frames]) subst_rhs, rest_src_rhs) in
  let () = debug (fun _ -> "Rest: " ^ Seq.to_string rest_src_seq) in
  (* Construct the rule sequence *)
  Rule.compose_pairwise
    (Rule.mk_infrule (apply_lemma defs (lemma_seq, cont_seq, rest_src_lhs)))
    [ mk_backlink_rule_seq (trm_theta, tag_theta) lemma_seq (Form.empty, Form.empty) false (targ_idx, targ_seq)
    ; Rule.identity ]

type backlink_t = FULL of Rule.t | PARTIAL of Rule.t

let dest_taggedrule = function FULL r -> r | PARTIAL r -> r

let cmp_taggedrule r r' =
  match (r, r') with
  | FULL _, PARTIAL _ -> -1
  | PARTIAL _, FULL _ -> 1
  | _ -> 0

(* If there is a backlink achievable through substitution and classical   *)
(* weakening (possibly after applying a lemma), then make the proof steps *)
(* that achieve it explicit so that actual backlinking can be done on     *)
(* Seq.equal sequents *)
let dobackl defs idx prf =
  let ((src_lhs, src_rhs) as src_seq) = Proof.get_seq idx prf in
  let matches = matches src_seq in
  let targets = Rule.all_nodes idx prf in
  let apps =
    Blist.bind
      (fun idx' -> Blist.map (Pair.mk idx') (matches (Proof.get_seq idx' prf)))
      targets
  in
  let f (targ_idx, ((theta, tagpairs, mappings) as subst)) =
    let () = debug (fun _ -> "Constructing backlink") in
    let ((targ_lhs, targ_rhs) as targ_seq) = Proof.get_seq targ_idx prf in
    let () =
      debug (fun _ ->
          "Target seq is " ^ Int.to_string targ_idx ^ ": "
          ^ Seq.to_string targ_seq )
    in
    let () =
      debug (fun _ ->
          "Term Subst: " ^ Term.Map.to_string Term.to_string theta )
    in
    let () = debug (fun _ -> "Tag Subst: " ^ Tagpairs.to_string tagpairs) in
    let (_, mapping_l, mapping_r) = Blist.foldl (fun (left, mapping_l, mapping_r) mapping ->
      if left then
        if fst mapping = -2 then (false, mapping_l, mapping_r)
        else (true, mapping_l @ [mapping], mapping_r)
      else (false, mapping_l, mapping_r @ [mapping])
    ) (true, [], []) mappings in
    let ((_, mapped_src_lhs), (_, rest_src_lhs)) = Seq.partition_summands (targ_lhs, src_lhs) mapping_l in
    let ((mapped_src_rhs, _), (rest_src_rhs, _)) = Seq.partition_summands (src_rhs, targ_rhs) mapping_r in
    let subst_targ_lhs, _ =
      Seq.subst theta (Seq.subst_tags tagpairs targ_seq)
    in
    let () =
      debug (fun _ ->
          "\t" ^ "Checking for subsumption:" ^ "\n\t\t" ^ "subst_targ_lhs: "
          ^ Form.to_string subst_targ_lhs
          ^ "\n\t\t" ^ "src_lhs: " ^ Form.to_string src_lhs )
    in
    if Form.subsumed subst_targ_lhs mapped_src_lhs then
      let () = debug (fun _ -> "\t\t" ^ "FULL") in
      let theta, _ = Subst.partition theta in
      let tagpairs, _ = Tagpairs.partition_subst tagpairs in
      FULL
        (mk_backlink_rule_seq (theta, tagpairs) (mapped_src_lhs, mapped_src_rhs) (rest_src_lhs, rest_src_rhs) true (targ_idx, targ_seq))
    else
      let () = debug (fun _ -> "\t\t" ^ "PARTIAL") in
      PARTIAL (mk_lemma_rule_seq subst (mapped_src_lhs, mapped_src_rhs) (rest_src_lhs, rest_src_rhs) defs (targ_idx, targ_seq))
  in
  (* Although application of all the constructed rule sequences will *)
  (* succeed by construction the backlinking may fail to satisfy the *)
  (* soundness condition, and so we pick the first one that is sound *)
  (* and we also prefer full backlinking to lemma application        *)
  let rules =
    Blist.map dest_taggedrule
      (Blist.stable_sort cmp_taggedrule (Blist.map f apps))
  in
  Rule.first rules idx prf

(*sort lhs summand by number in increasing order (needed for unify algorithm)*)
let sort_rule (l, r) =
  try
    let (_, ls) = Form.dest_sum l in
    let do_sort = Blist.foldl (fun num h ->
      if h.Heap.num < num then -1. else h.Heap.num
    ) 0. ls in
    if do_sort >= 0. then []
    else
      let ls' = Blist.sort (fun h h' -> 
          if h.Heap.num == h'.Heap.num then 0
          else if h.Heap.num > h'.Heap.num then 1
          else -1
      ) ls in
      [ ( [ (Form.with_heapsums l [ls'], r), Form.tag_pairs l, Tagpairs.empty ] , "Sort LHS")]
  with Not_symheap_sum -> []

(*split all rhs summands in which an inductive predicate appears
  (TODO only ind pred summands (??))
  (TODO maybe not in lhs?)
  TODO constraints copy at split_sum -> no, delete this rule, only apply it when unfolding and at start
                         and in unify(?)
  TODO test if both w' in ListLen also works
  TODO split sum in unfolding
  TODO rewoek domain exact impl -> preds not domain exact at all ??
  TODO impl domain exact for sums? (same ptos/preds, only dom.exact preds, same pred vars)
  TODO if you define predicates lslen + ls then can you trivially assume ls proof? bzw. can you automatically generate a + predicate or check if this is the case?
  TODO make summands completely indifferent from each other (no shared vars, tags)
      NO does not work, but when substituting vars, do it only for the relevant summands, not whole formula!
      (check for rules) ODER DOCH?
  TODO id axiom to left empty axiom and id rule -> split summands?
*)
let split_sum_rule ((l, r) as seq) =
  try
    let ((_, ls), (_, rs)) = Seq.dest_sum seq in
    let do_split = Pair.disj (Pair.map (fun hs -> Blist.exists (fun h -> h.Heap.num <> 1.) hs) (ls, rs)) in
    if do_split then
      ((*print_endline (Seq.to_string (Seq.split_sum seq));*)
      [ ( [ Seq.split_sum seq, Form.tag_pairs l, Tagpairs.empty ] , "Split Sum")])
    else []
  with Not_symheap_sum -> []


(* let axioms = ref (Rule.first [id_axiom ; ex_falso_axiom]) *)
let axioms = ref Rule.fail

let rules = ref Rule.fail

let use_invalidity_heuristic = ref false

let setup defs =
  preddefs := defs ;
  (*let sort_rule_seq = [Rule.mk_infrule sort_rule] in*)
  rules :=
    Rule.first
      ([ lhs_disj_to_symheaps
      ; rhs_disj_to_symheaps ]
      (*@ sort_rule_seq*) @
      [ lhs_instantiate
      ; simplify
      ; bounds_intro
      ; constraint_match_tag_instantiate
      ; upper_bound_tag_instantiate
      ; Rule.choice
          [ dobackl defs
          ; pto_intro_rule
          ; pred_intro_rule defs
          ; instantiate_pto
          ; Rule.conditional
              (fun (_, (cs, rs)) ->
                (*let res = Ord_constraints.for_all
                  (fun c ->
                    Tags.exists Tags.is_free_var (Ord_constraints.Elt.tags c)
                  ) cs in
                  (*print_endline ("NOOOOOOO " ^ string_of_bool res ^ " : " ^ Ord_constraints.to_string cs ^ " ; " ^ Heapsum.to_string (Blist.nth rs 0));
                  *)res*)true
              )
              (ruf defs)
          ; luf defs ] ]) ;
  let axioms = Rule.first [id_axiom; ex_falso_axiom] in
  rules := Rule.combine_axioms axioms !rules ;
  (*if !use_invalidity_heuristic then
    rules := Rule.conditional (fun s -> not (Invalid.check defs s)) !rules*)
