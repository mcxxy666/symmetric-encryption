
open Datatype

(***************************     pprint    ****************************)

(*** parency priority? ***)

let prec_out = 5
let prec_in = 5
let prec_par = 2
let prec_rep = 4
let prec_nu = 1
let prec_check = 2
let prec_dec = 2
let prec_case = 3
let prec_split = 2
let prec_begin = 2
let prec_end = 2
let prec_copy = 4

(*** pretty printer ***)

let rec print_stype t =
  match t with
  | TUnit -> "()"
  | TName Pub -> "Name(Pub)"
  | TName Pr -> "Name(Pr)"
  | TPair (t1, t2) -> "(" ^ print_stype t1 ^ "*" ^ print_stype t2 ^ ")"
  | TVari (t1, t2) -> "(" ^ print_stype t1 ^ "+" ^ print_stype t2 ^ ")"
  | TSKey ty -> "SymKey(" ^ print_stype ty ^ ")"
  | TEKey ty -> "EenKey(" ^ print_stype ty ^ ")"
  | TDKey ty -> "DecKey(" ^ print_stype ty ^ ")"
  | TChan ty -> "Ch(" ^ print_stype ty ^ ")"
  | TVar n -> "T" ^ string_of_int n

let print_exname x = match x with ENname s -> s | ENindex n -> string_of_int n

let rec print_message m =
  match m with
  | Name x -> print_exname x
  | Unit -> "()"
  | Pair (m1, m2) -> "(" ^ print_message m1 ^ "," ^ print_message m2 ^ ")"
  | EncSym (m, k) -> "{" ^ print_message m ^ "}_" ^ print_message k
  | EncAsym (m, k) -> "{{" ^ print_message m ^ "}}_" ^ print_message k
  | Inl m -> "inl(" ^ print_message m ^ ")"
  | Inr m -> "inr(" ^ print_message m ^ ")"

let rec print_efelem el =
  let print_atef a =
    match a with
    | AEend m -> "end(" ^ print_message m ^ ")"
    | AEchk (Pub, x, Emap e) ->
        "Chk_pub (" ^ print_exname x ^ ",[" ^ print_efelem e ^ "] )"
    | AEchk (Pr, x, Emap e) ->
        "Chk_pr (" ^ print_exname x ^ ",[" ^ print_efelem e ^ "] )"
    | AEchk (Pub, x, Evar n) ->
        "Chk_pub (" ^ print_exname x ^ ", e" ^ string_of_int n ^ ")"
    | AEchk (Pr, x, Evar n) ->
        "Chk_pr (" ^ print_exname x ^ ", e" ^ string_of_int n ^ ")"
    | AEchk (Pub, x, _) -> "Chk_pub (" ^ print_exname x ^ ", e)"
    | AEchk (Pr, x, _) -> "Chk_pr (" ^ print_exname x ^ ", e)"
  in
  match el with
  | (a, f) :: tl ->
      print_atef a ^ "->" ^ string_of_float f ^ " " ^ print_efelem tl
  | [] -> " "

let rec print_effect e =
  match e with
  | Emap el -> "([" ^ print_efelem el ^ "])"
  | Evar n -> "e" ^ string_of_int n
  | Eplus (e1, e2) -> "(" ^ print_effect e1 ^ "+" ^ print_effect e2 ^ ")"
  | Esub (i, x, ef) ->
      "([" ^ x ^ "/" ^ string_of_int i ^ "]" ^ print_effect ef ^ ")"

let rec print_etype t =
  match t with
  | ETUnit -> "()"
  | ETName (Pub, e1) ->
      if e1 = Emap [] then "Un" else "NPub(" ^ print_effect e1 ^ ")"
  | ETName (Pr, e1) -> "NPr(" ^ print_effect e1 ^ ")"
  | ETPair (t1, t2) -> "(" ^ print_etype t1 ^ "*" ^ print_etype t2 ^ ")"
  | ETVari (t1, t2) -> "(" ^ print_etype t1 ^ "\n\t\t+" ^ print_etype t2 ^ ")"
  | ETSKey ty -> "SKey(" ^ print_etype ty ^ ")"
  | ETEKey ty -> "EKey(" ^ print_etype ty ^ ")"
  | ETDKey ty -> "DKey(" ^ print_etype ty ^ ")"
  | ETChan ty -> "Ch(" ^ print_etype ty ^ ")"
  | ETany -> "Name"

let spf = Printf.sprintf

let print_list f l =
  match l with
  | [] -> ""
  | h :: t ->
      spf "%s%s" (f h)
        (List.fold_left (fun str x -> spf "%s, %s" str (f x)) "" t)

let print_atomic_constraint t =
  match t with
  | ECeq (e1, e2) -> spf "%s = %s" (print_effect e1) (print_effect e2)
  | ECsub (e1, e2) -> spf "%s >= %s" (print_effect e1) (print_effect e2)
  | ECnotin (x, e) -> spf "%s notin %s" (print_exname x) (print_effect e)
  | ECfn (e, ns) ->
      spf "FN(%s) ⊆ [%s]" (print_effect e) (print_list print_exname ns)

let print_ef_constraint t = print_list print_atomic_constraint t

let print_eenv (env : (id * etype) list) =
  print_list (fun (x, t) -> spf "(%s:%s)" x (print_etype t)) env

(*** pretty printer for processes ***)

let rec print_proc prec print_t p =
  match p with
  | Zero -> print_string "O"
  | Out (m, n) -> print_string (print_message m ^ "!" ^ print_message n)
  | OutS (m, n) -> print_string (print_message m ^ "!!" ^ print_message n)
  | In (m, x, t, pr) ->
      print_string (print_message m);
      print_string "?";
      (match print_t with
      | Some f -> print_string ("(" ^ x ^ ":" ^ f t ^ ")")
      | None -> print_string x);
      if pr = Zero then ()
      else (
        print_string ".\n";
        print_proc prec_in print_t pr)
  | InS (m, x, t, pr) ->
      print_string (print_message m);
      print_string "??";
      (match print_t with
      | Some f -> print_string ("(" ^ x ^ ":" ^ f t ^ ")")
      | None -> print_string x);
      if pr = Zero then ()
      else (
        print_string ".\n";
        print_proc prec_in print_t pr)
  | Par (pr1, pr2) ->
      if prec > prec_par then print_string "(";
      print_proc prec_par print_t pr1;
      print_string " |\n";
      print_proc prec_par print_t pr2;
      if prec > prec_par then print_string ")"
  | Nu (x, t, pr) ->
      print_string "(";
      (match print_t with
      | Some f -> print_string ("new " ^ x ^ ":" ^ f t)
      | None -> print_string ("new " ^ x));
      print_string ")\n";
      print_proc prec print_t pr
  | NuS (x, t, pr) ->
      print_string "(";
      (match print_t with
      | Some f -> print_string ("newS " ^ x ^ ":" ^ f t)
      | None -> print_string ("newS " ^ x));
      print_string ")\n";
      print_proc prec print_t pr
  | NuSym (x, t, pr) ->
      print_string "(";
      (match print_t with
      | Some f -> print_string ("newSym " ^ x ^ ":" ^ f t)
      | None -> print_string ("newSym " ^ x));
      print_string ")\n";
      print_proc prec print_t pr
  | NuAsym (x, t, y, t2, pr) ->
      print_string "(";
      (match print_t with
      | Some f ->
          print_string ("newAsym " ^ x ^ ":" ^ f t ^ ",\n\t" ^ y ^ ":" ^ f t2)
      | None -> print_string ("newAsym " ^ x ^ ",\n\t" ^ y));
      print_string ")\n";
      print_proc prec print_t pr
  | Check (x, n, pr) ->
      if prec > prec_check then print_string "(";
      print_string ("check " ^ x ^ " is " ^ n ^ " in \n");
      print_proc prec_check print_t pr;
      if prec > prec_check then print_string ")"
  | Case (m, x, t1, pr1, y, t2, pr2) ->
      if prec > prec_case then print_string "(";
      print_string ("case " ^ print_message m ^ " is ");
      (match print_t with
      | Some f -> print_string ("inl(" ^ x ^ ":" ^ f t1 ^ ").\n\t\t")
      | None -> print_string ("inl(" ^ x ^ ").\n\t\t"));
      print_proc prec_case print_t pr1;
      print_string "\n\tis ";
      (match print_t with
      | Some f -> print_string ("inr(" ^ y ^ ":" ^ f t2 ^ ").\n\t\t")
      | None -> print_string ("inr(" ^ y ^ ").\n\t\t"));
      print_proc prec_case print_t pr2;
      if prec > prec_case then print_string ")"
  | DecSym (m, x, t, k, pr) ->
      if prec > prec_dec then print_string "(";
      print_string ("decrypt " ^ print_message m ^ " is ");
      (match print_t with
      | Some f -> print_string ("{" ^ x ^ ":" ^ f t ^ "}")
      | None -> print_string ("{" ^ x ^ "}"));
      print_string ("_" ^ print_message k ^ " in \n");
      print_proc prec_dec print_t pr;
      if prec > prec_dec then print_string ")"
  | DecAsym (m, x, t, k, pr) ->
      if prec > prec_dec then print_string "(";
      print_string ("decrypt " ^ print_message m ^ " is ");
      (match print_t with
      | Some f -> print_string ("{{" ^ x ^ ":" ^ f t ^ "}}")
      | None -> print_string ("{{" ^ x ^ "}}"));
      print_string ("_" ^ print_message k ^ " in \n");
      print_proc prec_dec print_t pr;
      if prec > prec_dec then print_string ")"
  | Split (m, x, t1, y, t2, pr) ->
      if prec > prec_split then print_string "(";
      print_string ("split " ^ print_message m ^ " is ");
      (match print_t with
      | Some f ->
          print_string ("(" ^ x ^ ":" ^ f t1 ^ "," ^ y ^ ":" ^ f t2 ^ ") in \n")
      | None -> print_string ("(" ^ x ^ "," ^ y ^ ") in \n"));
      print_proc prec_split print_t pr;
      if prec > prec_split then print_string ")"
  | Match (m, x, y, t2, pr) ->
      if prec > prec_split then print_string "(";
      print_string ("match " ^ print_message m ^ " is ");
      (match print_t with
      | Some f -> print_string ("(" ^ x ^ "," ^ y ^ ":" ^ f t2 ^ ") in \n")
      | None -> print_string ("(" ^ x ^ "," ^ y ^ ") in \n"));
      print_proc prec_split print_t pr;
      if prec > prec_split then print_string ")"
  | Begin (m, pr) ->
      if prec > prec_begin then print_string "(";
      print_string ("begin " ^ print_message m ^ ".\n");
      print_proc prec_begin print_t pr;
      if prec > prec_begin then print_string ")"
  | End m ->
      print_string "(";
      print_string ("end " ^ print_message m ^ " )\n")
  | Copy pr ->
      print_string "*(";
      print_proc prec_begin print_t pr;
      print_string ")"

(***
   | Copy(pr) ->
         print_string "*";
         print_proc prec_copy print_t pr;

  ***)

(*** pretty printer for processes with indents ***)

let pp_nl indt = print_string ("\n" ^ indt)
let inc_indt indt = indt ^ "  "

let rec sizeof p =
  match p with
  | Zero -> 0
  | Out (m, n) -> 1
  | OutS (m, n) -> 1
  | In (m, x, t, pr) -> 1 + sizeof pr
  | InS (m, x, t, pr) -> 1 + sizeof pr
  | Par (pr1, pr2) -> 1 + sizeof pr1 + sizeof pr2
  | Nu (x, t, pr) -> 2 + sizeof pr
  | NuSym (x, t, pr) -> 2 + sizeof pr
  | NuAsym (x, t, y, t2, pr) -> 4 + sizeof pr
  | Check (x, n, pr) -> 2 + sizeof pr
  | Case (m, x, t1, pr1, y, t2, pr2) -> 5 + sizeof pr1 + sizeof pr2
  | NuS (x, t, pr) -> 2 + sizeof pr
  | DecSym (m, x, t, k, pr) -> 4 + sizeof pr
  | DecAsym (m, x, t, k, pr) -> 4 + sizeof pr
  | Split (m, x, t1, y, t2, pr) -> 5 + sizeof pr
  | Match (m, x, y, t2, pr) -> 5 + sizeof pr
  | Begin (m, pr) -> 1 + sizeof pr
  | End m -> 1
  | Copy pr -> 1 + sizeof pr

let rec pprint_proc indt prec size_lim print_t p =
  if sizeof p < size_lim then print_proc prec print_t p
  else
    match p with
    | Zero -> print_string "O"
    | Out (m, n) ->
        print_string (print_message m ^ "!" ^ print_message n);
        let indt' = inc_indt indt in
        pp_nl indt'
    | OutS (m, n) ->
        print_string (print_message m ^ "!!" ^ print_message n);
        let indt' = inc_indt indt in
        pp_nl indt'
    | In (m, x, t, pr) ->
        (print_string (print_message m);
         print_string "?";
         match print_t with
         | Some f -> print_string ("(" ^ x ^ ":" ^ f t ^ ")")
         | None -> print_string x);
        if pr = Zero then ()
        else (
          print_string ".";
          let indt' = inc_indt indt in
          pp_nl indt';
          pprint_proc indt' prec_in size_lim print_t pr)
    | InS (m, x, t, pr) ->
        (print_string (print_message m);
         print_string "??";
         match print_t with
         | Some f -> print_string ("(" ^ x ^ ":" ^ f t ^ ")")
         | None -> print_string x);
        if pr = Zero then ()
        else (
          print_string ".";
          let indt' = inc_indt indt in
          pp_nl indt';
          pprint_proc indt' prec_in size_lim print_t pr)
    | Par (pr1, pr2) ->
        if prec > prec_par then print_string "(";
        pprint_proc indt prec_par size_lim print_t pr1;
        print_string "  |  ";
        pp_nl indt;
        pprint_proc indt prec_par size_lim print_t pr2;
        if prec > prec_par then print_string ")"
    | Nu (x, t, pr) ->
        (print_string "(";
         match print_t with
         | Some f -> print_string ("new " ^ x ^ ":" ^ f t)
         | None -> print_string ("new " ^ x));
        print_string ")";
        pp_nl indt;
        pprint_proc indt prec size_lim print_t pr
    | NuS (x, t, pr) ->
        (print_string "(";
         match print_t with
         | Some f -> print_string ("newS " ^ x ^ ":" ^ f t)
         | None -> print_string ("newS " ^ x));
        print_string ")";
        pp_nl indt;
        pprint_proc indt prec size_lim print_t pr
    | NuSym (x, t, pr) ->
        (print_string "(";
         match print_t with
         | Some f -> print_string ("newSym " ^ x ^ ":" ^ f t)
         | None -> print_string ("newSym " ^ x));
        print_string ")";
        pp_nl indt;
        pprint_proc indt prec size_lim print_t pr
    | NuAsym (x, t, y, t2, pr) ->
        (print_string "(";
         match print_t with
         | Some f ->
             print_string ("newAsym " ^ x ^ ":" ^ f t ^ ",\n\t" ^ y ^ ":" ^ f t2)
         | None -> print_string ("newAsym " ^ x ^ ",\n\t" ^ y));
        print_string ")";
        pp_nl indt;
        pprint_proc indt prec size_lim print_t pr
    | Check (x, n, pr) ->
        if prec > prec_check then print_string "(";
        print_string ("check " ^ x ^ " is " ^ n ^ " in ");
        let indt' = inc_indt indt in
        pp_nl indt';
        pprint_proc indt' prec_check size_lim print_t pr;
        if prec > prec_check then print_string ")"
    | Case (m, x, t1, pr1, y, t2, pr2) ->
        let indt' = inc_indt indt in
        if prec > prec_case then print_string "(";
        print_string ("case " ^ print_message m ^ " is ");
        (match print_t with
        | Some f -> print_string ("inl(" ^ x ^ ":" ^ f t1 ^ ").")
        | None -> print_string ("inl(" ^ x ^ ")."));
        pp_nl indt';
        pprint_proc indt' prec_case size_lim print_t pr1;
        pp_nl indt';
        print_string " is ";
        (match print_t with
        | Some f -> print_string ("inr(" ^ y ^ ":" ^ f t2 ^ ").")
        | None -> print_string ("inr(" ^ y ^ ")."));
        pp_nl indt';
        pprint_proc indt' prec_case size_lim print_t pr2;
        pp_nl indt';
        if prec > prec_case then print_string ")"
    | DecSym (m, x, t, k, pr) ->
        if prec > prec_dec then print_string "(";
        print_string ("decrypt " ^ print_message m ^ " is ");
        (match print_t with
        | Some f -> print_string ("{" ^ x ^ ":" ^ f t ^ "}")
        | None -> print_string ("{" ^ x ^ "}"));
        print_string ("_" ^ print_message k ^ " in ");
        let indt' = inc_indt indt in
        pp_nl indt';
        pprint_proc indt' prec_dec size_lim print_t pr;
        if prec > prec_dec then print_string ")"
    | DecAsym (m, x, t, k, pr) ->
        if prec > prec_dec then print_string "(";
        print_string ("decrypt " ^ print_message m ^ " is ");
        (match print_t with
        | Some f -> print_string ("{{" ^ x ^ ":" ^ f t ^ "}}")
        | None -> print_string ("{{" ^ x ^ "}}"));
        print_string ("_" ^ print_message k ^ " in ");
        let indt' = inc_indt indt in
        pp_nl indt';
        pprint_proc indt' prec_dec size_lim print_t pr;
        if prec > prec_dec then print_string ")"
    | Split (m, x, t1, y, t2, pr) ->
        if prec > prec_split then print_string "(";
        print_string ("split " ^ print_message m ^ " is ");
        (match print_t with
        | Some f ->
            print_string ("(" ^ x ^ ":" ^ f t1 ^ "," ^ y ^ ":" ^ f t2 ^ ") in ")
        | None -> print_string ("(" ^ x ^ "," ^ y ^ ") in "));
        let indt' = inc_indt indt in
        pp_nl indt';
        pprint_proc indt' prec_split size_lim print_t pr;
        if prec > prec_split then print_string ")"
    | Match (m, x, y, t2, pr) ->
        if prec > prec_split then print_string "(";
        print_string ("match " ^ print_message m ^ " is ");
        (match print_t with
        | Some f -> print_string ("(" ^ x ^ "," ^ y ^ ":" ^ f t2 ^ ") in ")
        | None -> print_string ("(" ^ x ^ "," ^ y ^ ") in "));
        let indt' = inc_indt indt in
        pp_nl indt';
        pprint_proc indt' prec_split size_lim print_t pr;
        if prec > prec_split then print_string ")"
    | Begin (m, pr) ->
        if prec > prec_begin then print_string "(";
        print_string ("begin " ^ print_message m ^ ".");
        let indt' = inc_indt indt in
        pp_nl indt';
        pprint_proc indt' prec_begin size_lim print_t pr;
        if prec > prec_begin then print_string ")"
    | End m ->
        print_string "(";
        print_string ("end " ^ print_message m ^ " )\n")
    | Copy pr ->
        print_string "*(";
        print_proc prec_begin print_t pr;
        print_string ")"

let pp_proc print_t p = pprint_proc "" 0 7 print_t p
let ppp_proc p = pp_proc (Some print_stype) p
let pp_eproc p = pp_proc (Some print_etype) p

let print_env (env : (ex_name * stype) list) =
  let rec print_env' (env : (ex_name * stype) list) =
    match env with
    | [] -> ""
    | (x, t) :: tl ->
        print_exname x ^ ":" ^ print_stype t ^ "\n" ^ print_env' tl
  in
  print_string "Environment:\n";
  print_string (print_env' env);
  print_string "End of Environment:\n"

let print_constraint (env : (stype * stype) list) =
  let rec print_env' (env : (stype * stype) list) =
    match env with
    | [] -> ""
    | (x, t) :: tl ->
        print_stype x ^ " == " ^ print_stype t ^ "\n" ^ print_env' tl
  in
  print_string "Constraint :\n";
  print_string (print_env' env);
  print_string "End of Constraint:\n"

let print_constraint_name n m =
  print_string ("[" ^ n ^ "]");
  print_string " ";
  print_constraint m

let print_env_name n m =
  print_string ("[" ^ n ^ "]");
  print_string " ";
  print_env m

let print_pp (pp : pp) = match pp with Pub -> "Pub" | Pr -> "Pri"
let print_pp (pp : pp) = match pp with Pub -> "Pub" | Pr -> "Pri"

let print_stype_pp (pp : stype * pp) =
  let t, pp = pp in
  Printf.sprintf "%s(%s)" (print_pp pp) (print_stype t)
(* print_stype t ^ "[" ^ print_pp pp ^ "]" *)

let print_pp_list (pp_list : (stype * pp) list) =
  let rec print_pp_list' (pp_list : (stype * pp) list) =
    match pp_list with
    | [] -> ""
    | hd :: tl -> print_stype_pp hd ^ "\n" ^ print_pp_list' tl
  in
  print_string "PP List:\n";
  print_string (print_pp_list' pp_list);
  print_string "End of PP List\n"

let print_pp_list_name n m =
  print_string ("[" ^ n ^ "]");
  print_string " ";
  print_pp_list m

(*
  let print_constraint (env : constraint) = 
    let rec print_env' (env : constraint) = 
      match env with
    | [] -> ""
    | (x,t,p)::tl -> 
      (print_stype x)^":"^(print_stype t)^"  // from process: "^p^"\n"^(print_env' tl)
    in 
    (print_string "Constraint :\n";
    print_string (print_env' env);
    print_string "End of Constraint:\n")
    *)
