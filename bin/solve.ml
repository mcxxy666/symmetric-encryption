(* open Glpk;; *)
open Poly
open Z3

exception Unsatisfiable

(* type checker domain Poly ->(normalized) list or array of float ->(make_solver) z3 model -> float array solution *)

let ctx = mk_context [] 
let f64_sort = Z3.FloatingPoint.mk_sort_64 ctx
let to_real_expr (i: float) = Z3.FloatingPoint.mk_to_real ctx (Z3.FloatingPoint.mk_numeral_f ctx i f64_sort)

let rec zipWith f xs ys = match xs, ys with
  | [], [] -> []
  | x::xs, y::ys -> (f x y) :: zipWith f xs ys
  | _ -> failwith "zipWith: lists have different lengths"
(* make z3 expression from coeffs and uppoer bounds *)
let mk_item (coeff: float) (var : Expr.expr)  : Expr.expr 
  = Z3.Arithmetic.mk_mul ctx [to_real_expr coeff; var] 

let create_vars (n : int) = 
  let rec create_vars' n = 
    if n = 0 then [] else
      let var_name = "x" ^ string_of_int n in
      let var = Arithmetic.Real.mk_const_s ctx var_name in
      var :: create_vars' (n-1)
  in create_vars' n
let mk_lhs (coeffs: float list) (vars : Expr.expr list) : Expr.expr = Z3.Arithmetic.mk_add ctx (zipWith mk_item coeffs vars)

let make_ineq_z3 (coeffs: float list) (vars : Expr.expr list) (pbounds : float * float): Expr.expr = 
  let rhs = to_real_expr (snd pbounds) in
  Z3.Arithmetic.mk_le ctx (mk_lhs coeffs vars) rhs

let concatStringMap f xs = String.concat ";" (List.map f xs)

let check_raise (solver) : unit = 
  match Z3.Optimize.check solver with
  | Z3.Solver.SATISFIABLE -> print_endline "SATISFIABLE"
  | Z3.Solver.UNSATISFIABLE -> raise Unsatisfiable
  | Z3.Solver.UNKNOWN -> failwith "Z3 returned UNKNOWN"

let make_solver (objcoef : float array) (constrs : float array array) (pbounds : (float * float) array): float list
  = let n = Array.length objcoef in
    let xs = create_vars n in
    let ineqs = 
      zipWith (fun c p -> make_ineq_z3 (Array.to_list c) xs p) 
        (Array.to_list constrs) (Array.to_list pbounds) in 
    let obj = mk_lhs (Array.to_list objcoef) xs in
    let optimizer = Z3.Optimize.mk_opt ctx in
    (* let solver = Solver.mk_simple_solver ctx in *)

    (* x's domain *)
    Z3.Optimize.add optimizer (List.map (fun x -> (Z3.Arithmetic.mk_ge ctx x (to_real_expr 0.0))) xs);

    (* inequations *)
    Z3.Optimize.add optimizer ineqs;
    let _= Z3.Optimize.minimize optimizer obj in 

      (* print_endline  *)
      (* 'a option -> 'a *)
      (* print_endline (Z3.Solver.string_of_status (Z3.Optimize.check optimizer)); *)
      check_raise optimizer;
      (* 'a option -> 'a *)
      let model = Option.get (Z3.Optimize.get_model optimizer) in
      (* print_endline (Z3.Model.to_string model); *)
      (* print_endline (concatStringMap (fun x -> FuncDecl.to_string x) (Z3.Model.get_const_decls model)); *)
      let sol = (List.map (fun x -> float_of_string @@ Z3.Expr.to_string @@ Option.get @@ Z3.Model.get_const_interp_e model x) xs) in 
      (* print_endline (concatStringMap string_of_float sol); *)
      sol
    

let debug = Utilities.debug

 (*** (printf "Ill-typed.@\n"; lp) ***)

let array_of_ineq renaming ineq =
  match ineq with
    | Le(P(ps, 0.0), c) ->
	let nvar = List.length renaming in
	let a = Array.make nvar 0.0 in
	  List.iter 
	    (fun (ovi, f) -> 
	       let i = List.assoc ovi renaming in
		 a.(i) <- f) 
	    ps;
	  a, c
    | _ -> failwith "array_of_ineq: inequality is not normalized."



(***
let sanity_check_lca ineq =
  match ineq with
    Le(p, _) -> if iszero(p) then raise ZeroLC else ()
  | Lt(p, _) -> if iszero(p) then raise ZeroLC else ()

let sanity_check lc =
  List.map sanity_check_lca lc;;
***)

exception UnsatisfiableConstraints;;
let is_neg (P(l, c)) =
    List.for_all (fun (_,a)->a<=0.0) l;;
let is_zero (P(l, c)) =
    List.for_all (fun (_,a)->a=0.0) l;;


let isnontrivial lca =
  match lca with
    Le(p, c) -> if is_zero(p) then 
                   if c>=0.0 then false else raise Unsatisfiable
                else not((is_neg(p)) && c>=0.0)
  | Lt(p, c) -> if is_zero(p) then 
                   if c>0.0 then false else raise Unsatisfiable
                else
                   true



let zeroineq ineq =
  match ineq with
   Le(P(l, c1), c2) -> 
       (List.for_all (fun (_,a)-> a>= 0.0) l)&&(c2-.c1=0.0)
  | _ -> false

let pv_in_ineq ineq =
  match ineq with
   Le(P(l, c1), c2) -> 
       List.map fst (List.filter (fun (_,a)->a>0.0) l)
  | _ -> []

let fv_in_ineq ineq =
  match ineq with
   Le(P(l, c1), c2) -> 
       List.map fst l
  | Lt(P(l, c1), c2) -> 
       List.map fst l

let rec fv_in_ineqs ineqs =
  match ineqs with
    [] -> []
  | ineq::ineqs' ->
       let vs1 = fv_in_ineq ineq in
       let vs2 = fv_in_ineqs ineqs' in
         Utilities.merge_and_unify compare vs1 vs2

let subst_zvars_ineq ineq htab =
  match ineq with
   Le(P(l,c1), c2) ->
      let l' = List.filter (fun (v,_) -> not(Hashtbl.mem htab v)) l in
        Le(P(l',c1),c2)
 | Lt(P(l,c1), c2) ->
      let l' = List.filter (fun (v,_) -> not(Hashtbl.mem htab v)) l in
        Le(P(l',c1),c2)

(***
let subst_zvars zvars ineqs =
  List.map (subst_zvars_ineq zvars) ineqs
***)

let rec register_zvars zvars htab =
  match zvars with
    [] -> ()
  | v::zvars' ->
       (if Hashtbl.mem htab v then ()
        else Hashtbl.add htab v ();
        register_zvars zvars' htab)

(***
let rec find_zvars ineqs htab =
  match ineqs with
    [] -> []
  | ineq::ineqs' ->
       let 
         ineqs1 = find_zvars ineqs' htab
       in   
       let ineq1 = subst_zvars_ineq ineq htab in
         if zeroineq(ineq1) then
            let zvars2 = pv_in_ineq ineq1 in
              (register_zvars zvars2 htab;
               ineqs1)
         else
            ineq1::ineqs1
***)

let rec find_zvars ineqs htab res =
  match ineqs with
    [] -> res
  | ineq::ineqs' ->
       let ineq1 = subst_zvars_ineq ineq htab in
         if zeroineq(ineq1) then
            let zvars2 = pv_in_ineq ineq1 in
              (register_zvars zvars2 htab;
               find_zvars ineqs' htab res)
         else
            find_zvars ineqs' htab (ineq1::res)

let rec simplify_ineqs ineqs htab =
  let ineqs1 = find_zvars ineqs htab [] in
    if List.length ineqs = List.length ineqs1
    then 
      let ineqs2 = List.filter (fun lc -> isnontrivial(lc)) ineqs1 in 
      (ineqs2, fv_in_ineqs ineqs2)
    else
       simplify_ineqs ineqs1 htab

let rec solve ineqs ovids =
(***  let ineqs' = List.filter (fun lc -> isnontrivial(lc)) ineqs in ***)
  let htab = Hashtbl.create (List.length ovids) in
  let (ineqs', ovids') = simplify_ineqs ineqs htab in
  let _ = print_string ("# of linear constraints (after simplification):"^(string_of_int (List.length ineqs'))^"\n") in
  (* a map from ownership variables to integers that represent
     variables in GLPK solver *)
  if ineqs'=[] then (** trivial constraint **)
      ([], [||])
  else
    (* [112321,223,3231,512] <-> [0,1,2,3]  *)
  let renaming =
    let cnt = ref 0 in
      List.map (fun ovid -> let ret = ovid, !cnt in incr cnt; ret) ovids'
  in
  (* opbject = x0 + x1 + ...  *)
  (* minimize opbject *)
  let objcoef =
    let z = Array.make (List.length renaming) 0.0 in
      List.iter 
	(fun ovi ->
	   let i = List.assoc ovi renaming in
	     z.(i) <- 1.0)
	(List.map fst renaming);
      z
  in
  let array_l, ubounds = 
    List.fold_right 
      (fun ineq (arrays, ubounds) -> 
	 let array, ubound = array_of_ineq renaming ineq in
	   array::arrays, ubound::ubounds)
      ineqs'
      ([], [])
  in
  let constrs = Array.of_list array_l in
  let pbounds =
    let p = Array.make (List.length ubounds) (-.infinity, 0.0) in
      ignore(List.fold_left 
	       (fun i ub ->  p.(i) <- (-.infinity, ub); i + 1) 
	       0 
	       ubounds);
      p
  in
  let xbounds =
    Array.make (List.length renaming) (0.0, infinity)
  in

    (*  [0,1,2,3] <=> [1,2,3,5] *)
  let _ = print_string ("#objcoef:"^(string_of_int(Array.length objcoef))^"\n") in
  let _ = print_string ("#constrs:"^(string_of_int(Array.length constrs))^"\n") in
  let _ = print_string ("#pbounds:"^(string_of_int(Array.length pbounds))^"\n") in
  let _ = print_string ("#xbounds:"^(string_of_int(Array.length xbounds))^"\n") in
(* let make_solver (objcoef : float array) (constrs : float array array) (pbounds : (float * float) array)  (colNames : string list) *)
  (* let _ = debug "making a lp problem..." in make_solver objcoef constrs pbounds xbounds  *)
  let solution = make_solver objcoef constrs pbounds in 

  (* sol: [0,0,0,30] *)
  (* renaming: [0,1,2,3] <=> [1,2,3,5] *)

  (* [0,0,0,30] <=> [1,2,3,5] *)
  (* convert  col_primals to array*)
    (renaming, Array.of_list solution)

  (* let rev_renaming = List.map (fun (x, y) -> (y, x)) renaming in *)
  (* let col_names = List.map (fun (n, ovi) -> ("'o" ^ (string_of_int ovi))) rev_renaming in  *)
  (* let _ = make_solver (objcoef : float array) (constrs : float array array) (pbounds : (float * float) array)  *)
  (* let lp = make_problem Minimize objcoef constrs pbounds xbounds in *)
  (* let _ = debug "...created" in *)
    (* set_message_level lp 0;
    set_class lp Linear_prog; *)
    (* List.iter 
      (fun (n, ovi) -> 
	        set_col_name lp n ("'o" ^ (string_of_int ovi)))
      rev_renaming; *)
  (* let _ = debug "solving the problem..." in
    let lp = solve_lp constrs pbounds lp in
      (* If you want to output the generated linear programming problem, turn the flag on *)
  let _ = debug "...the problem has been solved" in
      if false then *)
	(* write_cplex lp "output.cplex"; *)
      (*********************
	   col_primals is an array of the calculated solution.
	   You can display the solution with, for example, the following program.

	   if false then
	     Array.iteri
	       (fun i f -> printf "'%a: %g@\n" print_ovid (List.assoc i rev_renaming) f)
	       col_primals; 
	*********************)
  (* get ineqs's solution *)
(**	(lp, (renaming, col_primals)) **)

