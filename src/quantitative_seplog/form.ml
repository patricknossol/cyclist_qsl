open Lib
open   Symbols

open Generic

open MParser

include Pair.Make (Ord_constraints) (Flist.Make (Heapsum))

let empty = (Ord_constraints.empty, [])

exception Not_symheap
exception Not_symheap_sum

let is_symheap = function _, [[s]] -> true | _ -> false

let dest : t -> Ord_constraints.t * Heap.t = function
  | cs, [s] -> (cs, Heapsum.dest s)
  | _ -> raise Not_symheap

let dest_sum : t -> Ord_constraints.t * Heapsum.t = function
  | cs, [s] -> (cs, s)
  | _ -> raise Not_symheap_sum

let constraints_sep cs =
  if Ord_constraints.is_empty cs then symb_nullstr else symb_colon

let pp fmt (cs, f) =
  let pp_or fmt () = Format.fprintf fmt " %s@ " symb_or.str in
  match f with
  | [] ->
      Format.fprintf fmt "@[%a%s%s@]" Ord_constraints.pp cs
        (constraints_sep cs).sep symb_false.str
  | _ ->
      Format.fprintf fmt "@[%a%s%a@]" Ord_constraints.pp cs
        (constraints_sep cs).sep
        (Blist.pp pp_or Heapsum.pp)
        f

let to_string (cs, hs) =
  let cs_str = Ord_constraints.to_string cs ^ (constraints_sep cs).sep in
  match hs with
  | [] -> cs_str ^ symb_false.str
  | hs -> cs_str ^ Blist.to_string symb_or.sep Heapsum.to_string hs

let terms (_, d) = Term.Set.union_of_list (Blist.map Heapsum.terms d)

let vars f = Term.filter_vars (terms f)

let tags (cs, d) =
  Tags.union_of_list (Ord_constraints.tags cs :: Blist.map Heapsum.tags d)

let tag_pairs f = Tagpairs.mk (tags f)

let inconsistent (cs, f) =
  Ord_constraints.inconsistent cs || Blist.for_all Heapsum.inconsistent f

let complete_tags avoid (cs, fs) =
  let fs =
    Blist.rev
      (Blist.foldr
        (fun f fs' ->
          let f' =
            if Heapsum.has_untagged_preds f then
              let avoid' = 
                Blist.foldl
                  (fun ts hs -> Tags.union ts (Heapsum.tags hs))
                  avoid (List.filter (fun p -> p <> f) fs') (*without f*) 
              in
              Heapsum.complete_tags avoid' f
            else f
          in f' :: fs' )
        (Blist.rev fs) [])
  in
  (cs, fs)

let subsumed_upto_constraints ?(total = true) (_, f) (_, f') =
  Blist.for_all
    (fun d2 -> Blist.exists (fun d1 -> Heapsum.subsumed ~total d1 d2) f)
    f'

let subsumed ?(total = true) ((cs, _) as l) ((cs', _) as r) =
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

let subsumed_upto_tags ?(total = true) (cs, hs) (cs', hs') =
  Blist.for_all
    (fun d2 ->
      Blist.exists (fun d1 -> Heapsum.subsumed_upto_tags ~total d1 d2) hs )
    hs'

let equal_upto_tags (cs, hs) (cs', hs') =
  Blist.for_all2 Heapsum.equal_upto_tags hs hs'

let parse ?(null_is_emp = false) ?(allow_tags = true) ?(augment_deqs = true) st
    =
  ( (if allow_tags then option Ord_constraints.parse else return None)
  >>= fun cs ->
  sep_by (Heapsum.parse ~allow_tags ~augment_deqs) (parse_symb symb_or)
  <?> "formula"
  >>= fun hs ->
  return
    ( Option.dest Ord_constraints.empty Fun.id cs
    , if null_is_emp && Blist.is_empty hs then [Heapsum.empty] else hs ) )
    st

let of_string ?(null_is_emp = false) s =
  handle_reply (MParser.parse_string (parse ~null_is_emp) s ())

let star ?(augment_deqs = true) (cs, f) (cs', g) =
  let constraints = Ord_constraints.union cs cs' in
  (constraints, Blist.map (
    fun (f', g') ->
      Heapsum.star ~augment_deqs f' g')
    (Blist.cartesian_product f g))

let disj (cs, f) (cs', g) = (Ord_constraints.union cs cs', f @ g)

let subst theta (cs, hs) = (cs, Blist.map (fun h -> Heapsum.subst theta h) hs)

let subst_existentials (cs, hs) = (cs, Blist.map Heapsum.subst_existentials hs)

let subst_tags tagpairs (cs, hs) =
  ( Ord_constraints.subst_tags tagpairs cs
  , Blist.map (Heapsum.subst_tags tagpairs) hs )

let norm (cs, hs) = (cs, Blist.map Heapsum.norm hs)

let with_constraints (_, hs) cs = (cs, hs)

let with_heapsums (cs, _) hs = (cs, hs)

let add_constraints (cs, hs) cs' = (Ord_constraints.union cs cs', hs)

let get_tracepairs f ((cs, _) as f') =
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

let rec is_domain_exact ?(covered = []) defs hss = 
  match hss with
    | (cs, hs :: []) -> 
      (match hs with
        | h :: [] ->
          (Tpreds.for_all (fun (_, (ident, _)) -> 
            if Blist.mem ident covered then true else
              let cases = Blist.filter_map (fun (sym, form) -> if sym = ident then Some(form) else None) defs in
              let covered = covered @ [ident] in
              Blist.for_all (fun case ->
                is_domain_exact ~covered:covered defs case
              ) cases
          ) h.Heap.inds)
        | _  -> false)
    | _ -> false
  
let mk_heap h =
  (Ord_constraints.empty, [[h]])

let mk_heapsums hss =
  (Ord_constraints.empty, hss)