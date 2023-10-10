open Utilities;;
open Datatype;;

let infer p =
  let t_start = Sys.time() in
  try 
  let _ = (print_string ("0: "^(string_of_float(Sys.time()))^"\n"); flush stdout) in
    let (p0, env) = Stype.stype_inf p in
    let _ = (Pprint.ppp_proc p0) in 
    let _ = (Pprint.print_env env) in
  let _ = (print_string ("1: "^(string_of_float(Sys.time()))^"\n"); flush stdout) in
    let (ec, p1) = Einf.einf env p0 in
  let _ = (print_string ("2: "^(string_of_float(Sys.time()))^"\n"); flush stdout) in
    let _ = print_string("# of effect constr.: "^(string_of_int (List.length ec))^"\n") in
    let (lc, emap, vars) = Reduce.ec2lc ec in
  let _ = (print_string ("3: "^(string_of_float(Sys.time()))^"\n"); flush stdout) in
    let _ = print_string("# of linear constr.: "^(string_of_int (List.length lc))^"\n") in
    let _ = print_string("# of variables: "^(string_of_int (List.length vars))^"\n") in
    let s = Solve.solve lc vars in
  let _ = (print_string ("4: "^(string_of_float(Sys.time()))^"\n"); flush stdout) in
    let emap' = Reduce.compute_ev emap vars s in
    let p' = map_proc (map_etype (Reduce.efsub emap')) p1 in
    let t_end = Sys.time() in
    let _ = print_string("Elapsed time: "^(string_of_float (t_end -. t_start))^"sec\n") in
      p'
  with
     e -> 
      let t_end = Sys.time() in
      let _ = print_string("Elapsed time: "^(string_of_float (t_end -. t_start))^"sec\n") in
        raise e

let parse in_strm =
  let lexbuf = Lexing.from_channel in_strm in
  let p =
    try
      Parser.main Lexer.token lexbuf
    with 
	Failure _ -> exit(-1) (*** exception raised by the lexical analyer ***)
      | Parsing.Parse_error -> (print_string "Parse error\n";exit(-1)) in
  let _ = 
    try
      close_in in_strm
    with
	Sys_error _ -> (print_string ("Cannot close file\n");exit(-1)) 
  in
    p
  

let parseFile filename =
  let in_strm = 
    try
      open_in filename 
    with
	Sys_error _ -> (print_string ("Cannot open file: "^filename^"\n");exit(-1)) in
  let _ = print_string ("analyzing "^filename^"...\n") in
    parse in_strm

(**
let parseFile filename =
  let in_strm = 
    try
      open_in filename 
    with
	Sys_error _ -> (print_string ("Cannot open file: "^filename^"\n");exit(-1)) in
  let _ = print_string ("analyzing "^filename^"...\n") in
  let lexbuf = Lexing.from_channel in_strm in
  let p =
    try
      Parser.main Lexer.token lexbuf
    with 
	Failure _ -> exit(-1) (*** exception raised by the lexical analyer ***)
      | Parsing.Parse_error -> (print_string "Parse error\n";exit(-1)) in
  let _ = 
    try
      close_in in_strm
    with
	Sys_error _ -> (print_string ("Cannot close file: "^filename^"\n");exit(-1)) 
  in
    p
**)
  
(*** main func.: %spica (filename) ***)
let main () =
  let _ = print_string "SPICA 2.1.1: a protocol verifier for SPI-Calculus with Correspondence Assertions\n" in
  let _ = flush stdout in
(**
  let filename =
    try
      Sys.argv.(1)
    with
	Invalid_argument _ -> (print_string "Usage: spica (filename)\n";exit(-1)) in
  let p = parseFile filename in
**)
  let p = 
     try
        parseFile Sys.argv.(1)
     with
	Invalid_argument _ -> parse stdin
  in
  let proc =
    try
      infer p 
    with 
	Solve.Unsatisfiable -> (print_string "The process is ill-typed.\n"; exit(-1))
      | Reduce.Unsatisfiable -> (print_string "The process is ill-typed.\n"; exit(-1))
      | Stype.Stype_failure _ -> (print_string "The process is not simply-typed.\n"; exit(-1))
      | Einf.TypeError _ -> (print_string "The process is not simply-typed.\n"; exit(-1))
   (***   | _ -> (print_string "Fatal error: please send a bug report\n"; exit(-1)) ***) in
   Pprint.pp_proc (Some Pprint.print_etype) proc; print_string "\n";;

if !Sys.interactive then
  ()
else
  main();;
