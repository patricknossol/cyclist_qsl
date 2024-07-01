open Lib
open   Symbols

open Generic

open MParser

include Pair.Make (Form) (Form)

let equal (l, r) (l', r') = Form.equal l l' && Form.equal r r'

let equal_upto_tags (l, r) (l', r') =
  Form.equal_upto_tags l l' && Form.equal_upto_tags r r'

let dest seq = Pair.map Form.dest seq

let dest_sum seq = Pair.map Form.dest_sum seq

let to_string (l, r) =
  Form.to_string l ^ symb_turnstile.sep ^ Form.to_string r

let pp fmt (l, r) =
  Format.fprintf fmt "@[%a %s@ %a@]" Form.pp l symb_turnstile.str Form.pp
    r

let parse ?(null_is_emp = false) st =
  ( Form.parse ~null_is_emp
  >>= (fun l ->
        parse_symb symb_turnstile
        >> ( Form.parse ~null_is_emp
           >>= fun r ->
           let tags = Tags.union (Form.tags l) (Form.tags r) in
           let l' = Form.complete_tags tags l in
           let inst_subst =
             Tagpairs.mk_free_subst tags (Tags.diff (Form.tags l') tags)
           in
           let l' = Form.subst_tags inst_subst l' in
           let r' = Form.complete_tags tags r in
           return (l', r') ) )
  <?> "Sequent" )
    st

let of_string ?(null_is_emp = false) s =
  handle_reply (MParser.parse_string (parse ~null_is_emp) s ())

let terms (l, r) = Term.Set.union (Form.terms l) (Form.terms r)

let vars seq = Term.filter_vars (terms seq)

let tags (l, r) = Tags.union (Form.tags l) (Form.tags r)

let tag_pairs (l, _) = Tagpairs.mk (Form.tags l)

let get_tracepairs (l, _) (l', _) =
  let tps = Form.get_tracepairs l l' in
  Pair.map (Tagpairs.filter (fun (t, _) -> Tags.is_free_var t)) tps

let subst theta seq = Pair.map (Form.subst theta) seq

let subst_tags tagpairs (l, r) =
  (Form.subst_tags tagpairs l, Form.subst_tags tagpairs r)

(* (l',r') *)
(* ------- *)
(* (l,r)   *)
(* meaning l  |- l' *)
(* and     r' |- r  *)

let subsumed (l, r) (l', r') = Form.subsumed l' l && Form.subsumed r r'

let norm s = Pair.map Form.norm s

let split_sum (((tl, (lc, lss)), (tr, (rc, rss))) as seq) =
  let seq_vars = ref (vars seq) in
  let (lss', rss') = Pair.map (fun hss ->
    Blist.map (fun hs ->
      Blist.flatten (Blist.map (fun h ->
        if Num.get_int h.Heap.num = 0 then [h] else
        let h_single = Heap.with_num h (1,0) in
        let hs' = Blist.foldl (fun hs' r ->
          let h' = Heap.copy_fresh_heap !seq_vars h_single in
          seq_vars := Term.Set.union !seq_vars (Heap.vars h');
          hs' @ [h']
        ) [h_single] (Blist.init ((Num.get_int h.Heap.num) - 1) (fun i -> Heap.empty))
        in
        hs'
      ) hs)
    ) hss
  ) (lss, rss) in
  ((tl, (lc, lss')), (tr, (rc, rss')))

let partition_summands (((tl, _), (tr, _)) as seq) mappings =
  try
    let (lc, ls), (rc, rs) = dest_sum seq in
    let mappings_sorted_l = Blist.sort (fun (a1, _) (a2, _) -> a1 - a2) mappings in
    let mappings_sorted_r = Blist.sort (fun (_, a1) (_, a2) -> a1 - a2) mappings in
    let rs1 = Blist.foldl (fun rs1 (l_ind, r_ind) -> 
      rs1 @ [Blist.nth rs r_ind]
    ) [] mappings_sorted_l in
    let (_, _, rs2) = Blist.foldl (fun (index, mappings, rs2) r -> 
      match mappings with 
        | mapping :: mappings' ->
          if index = snd mapping then
            (index + 1, mappings', rs2)
          else (index + 1, mappings, rs2 @ [r])
        | _ -> (index + 1, mappings, rs2 @ [r])
    ) (0, mappings_sorted_r, []) rs in
    let (_, _, ls1, ls2) = Blist.foldl (fun (index, mappings, ls1, ls2) l -> 
      match mappings with 
        | mapping :: mappings' ->
          if index = fst mapping then
            (index + 1, mappings', ls1 @ [l], ls2)
          else (index + 1, mappings, ls1, ls2 @ [l])
        | _ -> (index + 1, mappings, ls1, ls2 @ [l])
    ) (0, mappings_sorted_l, [], []) ls in
    (*let filter_constraints cs hs =
      Ord_constraints.filter (fun c -> Tags.exists (
        fun tag -> Tags.mem tag (Ord_constraints.Elt.tags c)
      ) (Heapsum.tags hs)) cs
    in
    let lc1 = filter_constraints lc ls1 in
    let rc1 = filter_constraints rc rs1 in
    let lc2 = filter_constraints lc ls2 in
    let rc2 = filter_constraints rc rs2 in
    (((lc1, [ls1]), (rc1, [rs1])), ((lc2, [ls2]), (rc2, [rs2])))*)
    (((tl, (lc, [ls1])), (tr, (rc, [rs1]))), ((tl, (lc, [ls2])), (tr, (rc, [rs2]))))
  with Form.Not_symheap_sum -> ((Form.empty, Form.empty), seq)

let set_conform_lists defs (l, r) =
  let l = Form.set_conform_lists defs l in
  let r = Form.set_conform_lists defs r in
  (l, r)

let set_precise_preds defs (l, r) =
  let l = Form.set_precise_preds defs l in
  let r = Form.set_precise_preds defs r in
  (l, r)

let reduce_zeros (l, r) =
  let l = Form.reduce_zeros l in
  let r = Form.reduce_zeros r in
  (l, r)

let rec gcd a = function
   0 -> a
 | b -> gcd b (a mod b)

let gcd_list = List.fold_left gcd 0

let rec pow a = function
  | 0 -> 1
  | 1 -> a
  | n -> 
    let b = pow a (n / 2) in
    b * b * (if n mod 2 = 0 then 1 else a)

let scale_float_to_int (i, f) power =
  if f <= 0 then i * (pow 10 power) else
  let amount = String.length (string_of_int f) in
  (int_of_string ((string_of_int i) ^ (string_of_int f))) * (pow 10 (power - amount))

let scale_floats_to_ints float_list =
  let power = Blist.fold_left (fun max (i,f) ->
    let amount = String.length (string_of_int f) in
    if f > 0 && amount > max then amount else max
  ) 0 float_list in
  let list = Blist.map (fun num -> 
    scale_float_to_int num power
  ) float_list in
  (list, power)

let rational_to_natural_nums ((lt, (lc, lss)), (rt, (rc, rss))) =
  let lnums, rnums = Pair.map (fun hss ->
    Blist.flatten (Blist.map (fun hs ->
      Blist.map (fun h ->
        h.Heap.num
      ) hs
    ) hss )
  ) (lss, rss) in
  let scaled_floats, power = scale_floats_to_ints (lnums @ rnums) in
  let factor = gcd_list scaled_floats in
  if factor = 0 then ((lt, (lc, lss)), (rt, (rc, rss))) else
  let lss, rss = Pair.map (fun hss ->
    Blist.map (fun hs ->
      Blist.map (fun h -> 
        Heap.with_num h (((scale_float_to_int h.Heap.num power) / factor),0)
      ) hs
    ) hss  
  ) (lss, rss) in
  ((lt, (lc, lss)), (rt, (rc, rss)))