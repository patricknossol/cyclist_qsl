open Lib
open Generic
open Quantitative_seplog

let cl_sequent = ref ""

let defs_path = ref "examples/qsl.defs"

let parse_null_as_emp = ref false

(* switches controlling invalidity heuristic *)
let invalidity_check = ref false

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
        

let () =
  gc_setup () ;
  let spec_list = !F.speclist () in
  Arg.parse spec_list
    (fun _ -> raise (Arg.Bad "Stray argument found."))
    !F.usage ;
  let defs = Defs.of_channel (open_in !defs_path) in
  Rules.setup defs ;

  if(not !do_testing) then
    
    let () = (if String.equal !cl_sequent "" then
      F.die "-S must be specified." spec_list !F.usage ;) in
    
    let seq = Seq.of_string ~null_is_emp:!parse_null_as_emp !cl_sequent in

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

    let list_equality_test = false in

    if list_equality_test then
      
      let list = [1;2;3;4] in
      let dofold (r, r2) =
        Blist.foldr
          (fun element res -> 
            if element == r then true else res
          ) list false
      in
      let heap_preds = 
        Blist.foldr ( fun r list ->
          list @ [(r, r)]
        ) list [] in
      let res = Blist.for_all dofold heap_preds in
      print_endline ("Equality: " ^ string_of_bool res);
    
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

        if not (String.get test 0 = '/' || test = "") then

          let seq = Seq.of_string ~null_is_emp:!parse_null_as_emp test in
          
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
              match res with
                | _ -> print_endline "\n-----------------------------------------------------\n";
      
      ) tests