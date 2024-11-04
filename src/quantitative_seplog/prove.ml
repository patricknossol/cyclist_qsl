open Lib
open Generic
open Quantitative_seplog

let cl_sequent = ref ""

let defs_path = ref "examples/qsl.defs"

let parse_null_as_emp = ref false

(* switches controlling invalidity heuristic *)
let invalidity_check = ref false

let use_assignment_problem = ref false

let do_testing = ref false

module Prover = Prover.Make (Seq)
module F = Frontend.Make (Prover)

let () = F.maxbound := 0

let () =
  F.usage :=
    !F.usage
    ^ " [-D <file>] [-emp] [-Lem <int>] [-IC] [-IT] [-IP] [-SLCOMP file] [-S \
       <string>]"

let () =
  F.speclist :=
    let old_spec_thunk = !F.speclist in
    fun () ->
      old_spec_thunk ()
      @ [ ( "-D"
          , Arg.Set_string defs_path
          , ": read inductive definitions from <file>, default is "
            ^ !defs_path )
        ; ( "-emp"
          , Arg.Set parse_null_as_emp
          , "parse the empty string as the formula [emp] rather than [False], "
            ^ "default is "
            ^ string_of_bool !parse_null_as_emp )
        ; ( "-Lem"
          , Arg.Int Rules.set_lemma_level
          , ": specify the permissiveness of the lemma application strategy"
            ^ "\n"
            ^ Rules.lemma_option_descr_str () )
        (*; ( "-IC"
          , Arg.Set invalidity_check
          , ": run invalidity heuristic before search, default is "
            ^ string_of_bool !invalidity_check )
        ; ( "-IT"
          , Arg.Set Rules.use_invalidity_heuristic
          , ": run invalidity heuristic during search, default is "
            ^ string_of_bool !Rules.use_invalidity_heuristic )
        ; ( "-IP"
          , Arg.Set Invalid.partition_strengthening
          , ": use partition strengthening in invalidity heuristic, default is "
            ^ string_of_bool !Invalid.partition_strengthening )*)
        ; ( "-S"
          , Arg.Set_string cl_sequent
          , ": prove the SL sequent provided in <string>" )
        ; ( "-test"
          , Arg.Set do_testing
          , ": test qsl" ) ];;
        
let of_string str parse_fun =
  handle_reply (MParser.parse_string parse_fun str ())


let () =
  gc_setup () ;
  let spec_list = !F.speclist () in
  Arg.parse spec_list
    (fun _ -> raise (Arg.Bad "Stray argument found."))
    !F.usage ;
  let defs = Defs.of_channel (open_in !defs_path) in
  let defs_list = Blist.map (fun preddef ->
    let (rules, r) = Preddef.dest preddef in 
    Preddef.mk (Blist.map (fun indrule -> 
      let (hs, pred) = Indrule.dest indrule in
      let ((_, (_, hss)), _) = Seq.split_sum (Form.reduce_zeros (Form.mk_heapsums [hs]), Form.empty) in
      if Blist.length hss = 0 then Indrule.mk [Heap.mk_num (0,0)] pred
      else 
      let hs = Blist.nth hss 0 in
      let hs = Blist.map (fun h -> 
        Heap.with_inds h (Tpreds.map (fun (tag, (pred, conform_list)) ->
          let (_, (_, (_, conform_predsym_list))) = Preddef.dest (Defs.get_preddef (Pred.predsym pred) defs) in
          (tag, (pred, conform_predsym_list))
        ) (h.Heap.inds))
      ) hs in
      Indrule.mk hs pred
    ) rules, r)
  ) (Defs.to_list defs) in
  let defs = Defs.of_list defs_list in
  Rules.setup defs ;

  if(not !do_testing) then
    
    let () = (if String.equal !cl_sequent "" then
      F.die "-S must be specified." spec_list !F.usage ;) in
    
    let seq = Seq.of_string ~null_is_emp:!parse_null_as_emp !cl_sequent in
    let seq = Seq.reduce_zeros seq in
    let seq = Seq.set_conform_lists defs_list seq in
    let seq = Seq.set_precise_preds defs_list seq in
    let seq = Seq.rational_to_natural_nums seq in
    let seq = Seq.split_sum seq in

    let res =
      F.gather_stats (fun () ->
          (*if !invalidity_check && Invalid.check defs seq then None
          else*) Some (F.idfs !Rules.axioms !Rules.rules seq) )
    in
    match res with
    | Some None ->
        print_endline
          ( "NOT proved: " ^ Seq.to_string seq ^ " [invalid]" ) ;
        exit 255
    | _ ->
        let res = Option.flatten res in
        F.exit (F.process_result true seq res)

  (*-----------TESTING------------*)
  else

    if true then

      let rec do_test_rec seq rs indent =
        match rs with
        | (r, k) :: rs ->
          let seqs' = r seq in
          let (rs, _) = Blist.fold_left (fun (rs, i) seq' ->
            if not (k = 0 || i = k) then (rs, i + 1) else
            let () = print_endline (indent ^ ((snd seq') ^ "---------------------")) in
            let indent = indent ^ "    " in
            let rs = Blist.fold_left (fun rs (seq, tags1, tags2) -> 
              print_endline (indent ^ (Seq.to_string seq));
              do_test_rec seq rs indent
            ) rs (fst seq') in
            (rs, i + 1)
          ) (rs, 1) seqs' in
          (*print_endline (indent ^ "---------------------") ;*)
          print_endline "" ;
          rs
        | _ -> rs
      in

      let do_test title s rs = 
        print_endline title ;
        print_endline "" ;
        print_endline (Seq.to_string s) ;
        do_test_rec s rs ""
      in

      let pseq s =
        let seq = Seq.of_string ~null_is_emp:!parse_null_as_emp s in
        let seq = Seq.reduce_zeros seq in
        let seq = Seq.set_conform_lists defs_list seq in
        let seq = Seq.set_precise_preds defs_list seq in
        let seq = Seq.rational_to_natural_nums seq in
        let seq = Seq.split_sum seq in
        seq
      in

      let _inst = (Rules.lhs_instantiate_seq, 0) in
      let _simplify = (Rules.simplify_seq, 0) in
      let _ruf k = (Rules.ruf_test defs, k) in
      let _luf_solo k = (Rules.luf_rl defs, k) in
      let _luf k = (Rules.luf_test defs, k) in
      let _pto = (Rules.pto_test, 0) in
      let _pred = (Rules.pred_test defs, 0) in
      let _backl k s = (Rules.dobackl_test defs s, k) in
      let _none = ((fun seq -> []), 0) in

      let s = pseq "BinTreeSeg(a,b) * BinTreeSegHeight(b,c) |- BinTreeHeight(a)" in
      let s2 = pseq "BinTreeSegHeight(b,c) |- BinTreeHeight(b)" in
      let _ = do_test "0" s [
        _luf 1 ;
          _luf 0 ;
            _ruf 1 ; _none ;
            _ruf 2 ; _backl 0 s2;
              _none ;
              _none ;
            _ruf 3 ; _backl 0 s2 ;
              _none ;
              _none ;
          _ruf 2 ; _pto ; _backl 0 s;
            _none ;
            _none ;
          _ruf 3 ; _pto ; _backl 0 s
      ] in

      (*
      let _ = do_test "0" "0 * x->y + 0.28 * c->d |- 0.4 * x->y + 0.14 * a->b" [Rules.identity] in
      let _ = do_test "1" "x'->y * z'=y + h'->y |- a'->b" [Rules.lhs_instantiate_ex_vars] in
      let _ = do_test "2" "x->y * x=y + x->y |- z->y" [Rules.eq_subst_rule] in
      let _ = do_test "3" "x->y * x=y + x->y * x=y |- z->y" [Rules.eq_subst_rule] in
      let _ = do_test "4" "x'->y |- x'->y + x'->y * x'=y" [Rules.eq_ex_subst_rule] in
      let _ = do_test "5" "x->y * x=y * y=z + x->y |- x->y + x->y * x=z" [Rules.eq_simplify] in
      let _ = do_test "6" "x->y * x=y * y=z + x->y * x=y * y=z |- x->y + x->y * x=z" [Rules.eq_simplify] in
      (*let s = do_test "x->y |- x->y" Rules.norm in*)
      let _ = do_test "7" "x->y * a->b |- x->y * c->d" [Rules.pto_intro] in
      let _ = do_test "7" "x->y * a->b + x->z |- x->w * c->d + x->m" [Rules.pto_intro] in
      let _ = do_test "8" "x'=w' * x'->y * a->b |- w'->y * c->d" [Rules.pto_intro] in
      let _ = do_test "9" "x->y' * a->b |- x->y' * c->d" [Rules.pto_intro] in
      let _ = do_test "10" "x->y * a->b |- x->z' * c->z'" [Rules.pto_intro] in
      let _ = do_test "12" "x'->y |- e'->y' * c->e'" [Rules.instantiate_pto_wo_rule] in
      let _ = do_test "13" "ListLen(x,y) * a->b |- ListLen(x,y) * a->c" [(Rules.pred_intro defs)] in
      let _ = do_test "14" "ListLen(x,y) * a->b |- ListLen(x,z) * a->c" [(Rules.pred_intro defs)] in
      let _ = do_test "14" "ListLen(x,y) * a->b + ListLen(x,z) * a->b |- ListLen(x,y) * a->c + ListLen(x,y) * a->c" [(Rules.pred_intro defs)] in
      let _ = do_test "14" "ListLen(x,y) * a->b + ListLen(x,y) * a->b |- ListLen(x,y) * a->c + ListLen(x,y) * a->c" [(Rules.pred_intro defs)] in
      let _ = do_test "15" "a->b * ListLen(x,y) + c->d |- x->y" [(Rules.luf_rl defs)] in
      let _ = do_test "16" "x->y |- a->b * ListLen(x,y) + c->d" [(Rules.ruf_rl defs)] in
      let _ = do_test "17" "x->y |- ListLen(a,b) * ListLen(x,y) + c->d" [(Rules.ruf_rl defs)] in
      let _ = do_test "18" "x->y |- ListLen(a,nil) * ListLen(x,nil) + c->d" [(Rules.ruf_rl defs)] in
      let _ = do_test "19" "x->y |- ListLen(a',nil) * ListLen(x',nil) + c->d" [(Rules.ruf_rl defs)] in
      let _ = do_test "20" "x->y |- a->b' * ListLen(x',y) + c->d" [(Rules.ruf_rl defs)] in
      let _ = do_test "21" "x->y |- a'=y * a'->b' * ListLen(x',y) + c->d" [(Rules.ruf_rl defs)] in
      let _ = do_test "22" "x->y |- h->y' * a'=y' * a'->b' * ListLen(x',y) + c->d" [(Rules.ruf_rl defs)] in
      let _ = do_test "23" "x->y |- a'->b * ListLen(x',y) + c->d" [(Rules.ruf_rl defs)] in
      let _ = do_test "24" "a->b * b=z + c->d |- a->b + x->z" [Rules.split_id_summand] in
      let _ = do_test "25" "ListLen(a,b) + List(a,b) |- RListLen(x,z) + RList(x,z)" [(Rules.split_conform_predicate_summands defs)] in
      let _ = do_test "26" "x->y * ListLen(a,b) + x->y * List(a,b) |- y->z * RListLen(x,z) + y->z * RList(x,z)" [(Rules.split_conform_predicate_summands defs)] in
      let _ = do_test "27" "x->y * ListLen(a,b) + x->z * List(a,b) |- y->z * RListLen(x,z) + y->z * RList(x,z)" [(Rules.split_conform_predicate_summands defs)] in
      let _ = do_test "28" "ListLen(a,b) + List(a,c) |- RListLen(x,z) + RList(x,z)" [(Rules.split_conform_predicate_summands defs)] in
      let _ = do_test "29" "x->y' * ListLen(a,b) + x->z' * List(a,b) |- y->z * RListLen(x,z) + y->z * RList(x,z)" [(Rules.split_conform_predicate_summands defs)] in
      let _ = do_test "30" "x->y' * ListLen(a,b') + x->z' * List(a,c') |- RListLen(x,z) + RList(x,z)" [(Rules.split_conform_predicate_summands defs)] in
      [a] nil!=a * nil!=b * a!=b * a->w * b->c * ListLenTmp(w, b) + nil!=a * nil!=b * a!=b * a->x * b->c * ListTmp(x, b) |- [a'] a->w' * ListLenTmp(w', c) + a->w' * ListTmp(w', c)
      let _ = do_test "30" "nil!=a * nil!=b * a!=b * a->w * b->c * ListLenTmp(w, b) + nil!=a * nil!=b * a!=b * a->x * b->c * ListTmp(x, b) |- a->w' * ListLenTmp(w', c) + a->w' * ListTmp(w', c)" [(Rules.split_conform_predicate_summands defs)] in
      *)

      print_endline("FINISH")
      
    else 

      let read_file filename =
        let lines = ref[] in
        let chan = open_in filename in
        try
          while true; do
            lines := input_line chan :: !lines
          done; !lines
        with End_of_file ->
          close_in chan;
          List.rev !lines; in

      let tests = read_file "tests.txt" in

      Blist.iter (fun test ->

        if test = "" || String.get test 0 = '/' then
          ()
        else
          let seq = Seq.of_string ~null_is_emp:!parse_null_as_emp test in
          let seq = Seq.reduce_zeros seq in
          let seq = Seq.set_conform_lists defs_list seq in
          let seq = Seq.set_precise_preds defs_list seq in
          let seq = Seq.rational_to_natural_nums seq in
          let seq = Seq.split_sum seq in
          
          let res =
            F.gather_stats (fun () ->
                (*if !invalidity_check && Invalid.check defs seq then None
                else*) Some (F.idfs !Rules.axioms !Rules.rules seq) )
          in

          match res with
          | Some None ->
              print_endline
                ( "NOT proved: " ^ Seq.to_string seq ^ " [invalid]" ) ;
          | _ ->
              let res = Option.flatten res in
              let res = F.process_result true seq res in
              (if !Stats.do_statistics then
                print_endline (
                  "\nUNIFY TIME: " ^ string_of_float(1000. *. !Test_stats.unify_time)
                ^  "\nUNIFY CALLS: " ^ string_of_int(!Test_stats.unify_calls)
                ^ "\nUNIFY TIME: " ^ string_of_float(1000. *. !Test_stats.unify_time)
                ^ "\nAVG UNIFY TIME: " ^ string_of_float(1000. *. !Test_stats.unify_time /. (float_of_int !Test_stats.unify_calls))
                ^ "\nPERCENTAGE UNIFY TIME: " ^ string_of_float(100. *. !Test_stats.unify_time /. !Stats.Gen.cpu_time)
                );
                Stats.gen_print();
              );
              match res with
                | _ -> print_endline "\n-----------------------------------------------------\n";
      
      ) tests