open Lexing
open Lexer
open Z3api

(* report_error: string -> lexbuf -> string -> unit
Fucntion printing an error
Parameters:
  - filename: path of the file 
  - lexbuf: lexer buffer
  - msg: message to print
 *)
let report_error filename lexbuf msg =
  let (b,e) = (lexeme_start_p lexbuf, lexeme_end_p lexbuf) in
  let fc = b.pos_cnum - b.pos_bol + 1 in
  let lc = e.pos_cnum - b.pos_bol + 1 in
  Printf.eprintf "File \"%s\", line %d, characters %d-%d: %s\n" filename b.pos_lnum fc lc msg

let debug      = ref ""
let inputFile  = ref "<stdin>"
let bound      = ref 12
let do_dfs     = ref false
let upto_techs = ref "c"
let memo_size  = ref 10000

let parse_debug str =
  let contains c = String.contains str c in
  let f = contains 'f' in
  let c = contains 'c' in
  let t = contains 't' in
  let n = contains 'n' in
  (f,c,t,n)

let parse_upto str =
  let contains c = String.contains str c in
  let n = contains 'n' in
  let c = contains 'c' in
  (n,c)

let main =
  begin
    let def_msg_s = Printf.sprintf "%s (default: \"%s\")" in
    let def_msg_i msg i = def_msg_s msg (string_of_int i) in
    let speclist = [
        ("-d", Arg.Set_string debug,
         (def_msg_s "debug mode: e.g. \"fctn\" to print \n    [f]rontier length\n    [c]onfiguration pairs at each step\n    [t]race of final configurations\n    [n]ormalised configurations\n   " !debug));
        ("-i", Arg.Set_string (inputFile),
         (def_msg_s "input file" !inputFile));
        ("-b", Arg.Set_int (bound),
         (def_msg_i "bound for function applications" !bound));
        ("-dfs", Arg.Set (do_dfs),
         (def_msg_s "set LTS traversal to DFS" (if !do_dfs then "DFS" else "BFS")));
        ("-memo", Arg.Set_int (memo_size),
         (def_msg_i "size of memoisation map" !memo_size));
        ("-u", Arg.Set_string (upto_techs),
         (def_msg_s "up-to techniques enabled: e.g. \"nc\" for \n    [n]ormalisation\n    [c]all caching\n   "
            !upto_techs)) ]
    in
    let usage_msg = "Equivalence Checking Tool for Functional Programs" in
    Arg.parse speclist print_endline usage_msg;
    print_endline "****************";
    Printf.printf "Debug mode: %s\n" !debug;
    Printf.printf "Input file: %s\n" !inputFile;
    Printf.printf "Bound: %d\n"      !bound;
    Printf.printf "Traversal: %s\n" (if !do_dfs then "DFS" else "BFS");
    Printf.printf "Memoisation cache size: %d\n" !memo_size;
    Printf.printf "Up-to techniques: %s\n" !upto_techs;
    print_endline "****************";
    
    (* Opening the file *)
    let input = if (!inputFile = "<stdin>") then stdin else open_in !inputFile in
    (* Lexing *)
    let filebuf = Lexing.from_channel input in
    try
      (* Parsing *)
      let pgm = Parser.main Lexer.token filebuf  in
      (if !debug <> "" then print_endline "[parsing] File parsed");
      let pgm = Preprocess.assign_fresh_ids_to_names_pgm pgm in
      (if !debug <> "" then print_endline ("Program: \n" ^ (Ast.string_of_pgm pgm)));
      let pgm = Typing.type_pgm pgm (String.contains !debug 'y') in
      (if !debug <> "" then
         begin
           print_endline "[typing] File typed";
           print_endline ("Type: \n" ^ (Type.string_of_t (snd pgm.rel)));
           print_endline ("[z3] Z3 sanity check sat: ");
           let z3_test = (check_sat ((_int 42) ==. ((_sint "x") +. (_sint "y")))) in
           assert(z3_test);
           print_endline (string_of_bool z3_test);
           print_endline ("[z3] Z3 sanity check everything model:");
           let z3_model_test = (get_model_s ()) in
           print_endline (z3_model_test) ;
           print_endline ""
         end);
      let debug_flags = parse_debug !debug in
      let upto_flags = parse_upto !upto_techs in
      Lts.start_bisim
        pgm.e1
        pgm.e2
        !bound
        debug_flags
        !do_dfs
        !memo_size
        upto_flags
    with
    | Parser.Error ->
       Error.report_error_f_lex !inputFile (Lexer.get_lex_start_end_p filebuf) "Parsing Error."
    | Error.LexE (lex_pos, m)
      | Error.ParseE (lex_pos, m) ->
       Error.report_error_f_lex !inputFile lex_pos ("Parsing Error: " ^ m)
    | Error.SyntaxE (lex_pos_opt, m)
      | Error.TypeE (lex_pos_opt, m)
      | Error.RuntimeE (lex_pos_opt, m) ->
       begin
         match lex_pos_opt with
         | None -> Error.report_error_f !inputFile ("Typing Error: " ^ m)
         | Some lex_pos -> Error.report_error_f_lex !inputFile lex_pos ("Typing Error: " ^ m)
       end
  end

let () = main
