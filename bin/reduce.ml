open Datatype
open Utilities
open Poly


type msg = message
type substitutions = (index * msg) list
type atom = atomic_effect
exception Unsatisfiable


(** 
 ** get_substitutions:
 **       ef_constraints ->substitutions
 **)

let rec get_substitutions_from_ef e =
  match e with
     Eplus(e1,e2) -> 
       let s1 = get_substitutions_from_ef e1 in
       let s2 = get_substitutions_from_ef e2 in
         merge_and_unify compare s1 s2
   | Esub(ind,name,e) ->
       let s1 = get_substitutions_from_ef e in
       let s2 = [(ind,name)] in
         merge_and_unify compare s1 s2
   | _ -> []
       
       
let get_substitutions_from_eca eca =
  match eca with
    ECeq(e1, e2) -> 
       let s1 = get_substitutions_from_ef e1 in
       let s2 = get_substitutions_from_ef e2 in
         merge_and_unify compare s1 s2
  | ECsub(e1,e2) ->
       let s1 = get_substitutions_from_ef e1 in
       let s2 = get_substitutions_from_ef e2 in
         merge_and_unify compare s1 s2
  | ECnotin(_,e) -> 
       get_substitutions_from_ef e
  | ECfn(e,_) ->
       get_substitutions_from_ef e


let rec get_substitutions ec =
  match ec with
    [] -> []
  | eca::ec' ->
       let s1 = get_substitutions_from_eca eca in
       let s2 = get_substitutions ec' in
         merge_and_unify compare s1 s2

(*** replace_some_name_in_atom ***)
let rec replace_some_in_msg ind name m =
  match m with
    Unit -> [Unit]
  | Name(ENname(n)) ->
        if n=name then 
            merge_and_unify compare [Name(ENname(name))] [Name(ENindex(ind))]
        else
     
            [Name(ENname(n))]
  | Name(ENindex(i)) ->
            [Name(ENindex(i))]
  | Pair(m1,m2) ->
        let ms1 = replace_some_in_msg ind name m1 in
        let ms2 = replace_some_in_msg ind name m2 in
        let ms = List.flatten (List.map (fun m1' -> List.map (fun m2' -> Pair(m1',m2')) ms2) ms1) in
           List.sort compare ms
  | EncSym(m1,m2) ->
        let ms1 = replace_some_in_msg ind name m1 in
        let ms2 = replace_some_in_msg ind name m2 in
        let ms = List.flatten(List.map (fun m1' -> List.map (fun m2' -> EncSym(m1',m2')) ms2) ms1) in
           List.sort compare ms
  | EncAsym(m1,m2) ->
        let ms1 = replace_some_in_msg ind name m1 in
        let ms2 = replace_some_in_msg ind name m2 in
        let ms = List.flatten(List.map (fun m1' -> List.map (fun m2' -> EncAsym(m1',m2')) ms2) ms1) in
           List.sort compare ms

  | Inl(m') ->
       List.map (fun m1->Inl(m1)) (replace_some_in_msg ind name m')
  | Inr(m') ->
       List.map (fun m1->Inr(m1)) (replace_some_in_msg ind name m')

let rec replace_some_name_in_atom ind name atom =
  match atom with
    AEend(m) ->   
       let ms = replace_some_in_msg ind name m in
            List.map (fun m -> AEend(m)) ms
  | AEchk(l,ENname(n),e) ->
        if n=name then 
           merge_and_unify compare [AEchk(l,ENname(name),e)] [AEchk(l,ENindex(ind),e)]        else
            [AEchk(l,ENname(n),e)]
  | AEchk(l,ENindex(i),e) ->
            [AEchk(l,ENindex(i),e)];;


(** expand_atoms:
 **      substitutions -> atom list -> atom list
 **)
let rec expand_msg ind name m =
  match m with
    Unit -> [Unit]
  | Name(ENname(n)) ->
        if n=name then 
            merge_and_unify compare [Name(ENname(name))] [Name(ENindex(ind))]
        else
            [Name(ENname(n))]
  | Name(ENindex(i)) ->
        if i=ind then
            merge_and_unify compare [Name(ENname(name))] [Name(ENindex(ind))]
        else
            [Name(ENindex(i))]
  | Pair(m1,m2) ->
        let ms1 = expand_msg ind name m1 in
        let ms2 = expand_msg ind name m2 in
        let ms = List.flatten (List.map (fun m1' -> List.map (fun m2' -> Pair(m1',m2')) ms2) ms1) in
           List.sort compare ms
  | Inl(m') ->
       List.map (fun m1->Inl(m1)) (expand_msg ind name m')
  | Inr(m') ->
       List.map (fun m1->Inr(m1)) (expand_msg ind name m')
  | EncSym(m1,m2) ->
        let ms1 = expand_msg ind name m1 in
        let ms2 = expand_msg ind name m2 in
        let ms = List.flatten(List.map (fun m1' -> List.map (fun m2' -> EncSym(m1',m2')) ms2) ms1) in
           List.sort compare ms

  | EncAsym(m1,m2) ->
        let ms1 = expand_msg ind name m1 in
        let ms2 = expand_msg ind name m2 in
        let ms = List.flatten(List.map (fun m1' -> List.map (fun m2' -> EncAsym(m1',m2')) ms2) ms1) in
           List.sort compare ms

let rec expand_atom_by_as (ind, name) atom =
  match atom with
    AEend(m) -> 
         let ms = expand_msg ind name m in
            List.map (fun m -> AEend(m)) ms
  | AEchk(l,ENname(n),e) ->
        if n=name then 
            merge_and_unify compare [AEchk(l,ENname(name),e)] [AEchk(l,ENindex(ind),e)]
        else
            [AEchk(l,ENname(n),e)]
  | AEchk(l,ENindex(i),e) ->
        if i=ind then
            merge_and_unify compare [AEchk(l,ENname(name),e)] [AEchk(l,ENindex(ind),e)]
        else
            [AEchk(l,ENindex(i),e)];;

let rec expand_atom s atom =
  match s with
    [] -> [atom]
  | as1::s' ->
       let atoms1 = expand_atom_by_as as1 atom in
       let atoms2 = expand_atom s' atom in
           merge_and_unify compare atoms1 atoms2
     
let rec expand_atoms s atoms =
  match atoms with
    [] -> []
  | a::atoms' ->
       let atoms1 = expand_atom s a in
       let atoms2 = expand_atoms s atoms' in
           merge_and_unify compare atoms1 atoms2

(*** 
 *** get_atoms:
 ***      ef_constraints -> atom list
 ***)

let rec get_atoms_from_ef e =
  match e with
    Emap(l) ->
      delete_duplication_unsorted (List.map fst l)
  | Eplus(e1,e2) ->
      let atoms1 = get_atoms_from_ef e1 in
      let atoms2 = get_atoms_from_ef e2 in
         merge_and_unify compare atoms1 atoms2
  | Esub(_,_,e) ->
      get_atoms_from_ef e
  | _ -> []

let rec get_atoms_from_eca eca: atom list =
  match eca with
    ECeq(e1,e2) ->
      let atoms1 = get_atoms_from_ef e1 in
      let atoms2 = get_atoms_from_ef e2 in
         merge_and_unify compare atoms1 atoms2
  | ECsub(e1,e2) ->
      let atoms1 = get_atoms_from_ef e1 in
      let atoms2 = get_atoms_from_ef e2 in
         merge_and_unify compare atoms1 atoms2
  | ECnotin(_,e) ->
      get_atoms_from_ef e
  | ECfn(e,_) ->
      get_atoms_from_ef e

let rec get_atoms ec: atom list =
  match ec with
    [] -> []
  | eca::ec' ->
      let atoms1:atom list = get_atoms_from_eca eca in
      let atoms2:atom list = get_atoms ec' in
         merge_and_unify compare atoms1 atoms2

let rec get_closure atoms next =
     let atoms' = next atoms in
        if List.length atoms' = List.length atoms
        then atoms
        else get_closure atoms' next

let rec get_allatoms c =
  let atoms: atomic_effect list = get_atoms c in
  let s = get_substitutions c in
  let next = expand_atoms s in
      get_closure atoms next

(*** 
 *** get_efvars: ef_constraints ->evid list
 ***)
let rec get_efvars_from_ef e =
  match e with
    Emap(l) -> []
  | Evar(eid) -> [eid]
  | Eplus(e1,e2) ->
      let efvars1 = get_efvars_from_ef e1 in
      let efvars2 = get_efvars_from_ef e2 in
         merge_and_unify compare efvars1 efvars2
  | Esub(_,_,e) ->
      get_efvars_from_ef e

let rec get_efvars_from_eca eca =
  match eca with
    ECeq(e1,e2) ->
      let efvars1 = get_efvars_from_ef e1 in
      let efvars2 = get_efvars_from_ef e2 in
         merge_and_unify compare efvars1 efvars2
  | ECsub(e1,e2) ->
      let efvars1 = get_efvars_from_ef e1 in
      let efvars2 = get_efvars_from_ef e2 in
         merge_and_unify compare efvars1 efvars2
  | ECnotin(_,e) ->
      get_efvars_from_ef e
  | ECfn(e,_) ->
      get_efvars_from_ef e

let rec get_efvars ec =
  match ec with
    [] -> []
  | eca::ec' ->
      let evs1 = get_efvars_from_eca eca in
      let evs2 = get_efvars ec' in
         merge_and_unify compare evs1 evs2

(***  
 *** mk_evsubst: evid list ->atom list -> evmap
 ***)

let current_ovarid = ref 0;;
let new_ovar() =
  (current_ovarid := !current_ovarid+1;
   !current_ovarid);;

let rec mk_evsubst_for_each_efvar atoms ev =
  let map = List.map (fun a -> (a, new_ovar())) atoms in
     (ev, map)

type evmap = (eid* (atom * ovarid) list) list

let rec mk_evsubst evars atoms: evmap =
  List.map (mk_evsubst_for_each_efvar atoms) evars

(*** 
 *** eca2lc_atom:
 ***    ef_constraint -evmap -atom -linear_constraints
 ***)

let rec names_of_msg m =
  match m with
    Name(en) -> [en]
  | Unit -> []
  | Pair(m1,m2) ->
      let ns1 = names_of_msg m1 in
      let ns2 = names_of_msg m2 in
         merge_and_unify compare ns1 ns2
  | EncSym(m1,m2) -> 
      let ns1 = names_of_msg m1 in
      let ns2 = names_of_msg m2 in
         merge_and_unify compare ns1 ns2
  | Inl(m) -> names_of_msg m
  | Inr(m) -> names_of_msg m
  | EncAsym(m1,m2) -> 
      let ns1 = names_of_msg m1 in
      let ns2 = names_of_msg m2 in
         merge_and_unify compare ns1 ns2

let rec names_of_atom atom =
  match atom with
    AEend(m) -> names_of_msg m
  | AEchk(l,en,e) -> [en]

let name_in_atom n atom =
  List.mem n (names_of_atom atom)

let rec atom_sub_names atom ns =
  let ns' = names_of_atom atom in
    List.for_all (fun x-> List.mem x ns) ns';;

let rec eval_ef e evmap atom =
  match e with
    Emap(l) -> (try 
                 let n = List.assoc atom l in
                   int_poly(n)
                with
                 Not_found -> zero_poly)
  | Evar(ev) -> (try
                   let ov = List.assoc atom (List.assoc ev evmap) in
                   var_poly(ov)
                with
                 Not_found -> zero_poly)
  | Eplus(e1,e2) ->
        let p1 = eval_ef e1 evmap atom in
        let p2 = eval_ef e2 evmap atom in
           add_poly p1 p2
  | Esub(ind,n,e') ->
      if name_in_atom (ENindex ind) atom 
      then
         zero_poly
      else
        let atoms = replace_some_name_in_atom ind n atom in
        let ps = List.map (eval_ef e' evmap) atoms in
          List.fold_left add_poly zero_poly ps

let eca2lc_atom ac evmap atom =
    match ac with
        ECsub(e1,e2) ->
             let p1:poly = eval_ef e1 evmap atom in
             if p1=zero_poly then []
             else
             let p2 = eval_ef e2 evmap atom in
                 [Le(sub_poly p1 p2, 0.0)]
     | ECeq(e1,e2) ->
             let p1 = eval_ef e1 evmap atom in
             let p2 = eval_ef e2 evmap atom in
             if p1=zero_poly then
               if p2=zero_poly then
                  []
               else
                  [Le(p2, 0.0)]
             else if p2=zero_poly then
                  [Le(p1, 0.0)]
             else
               let p = sub_poly p1 p2 in
                 [Le(p, 0.0); Le(neg_poly(p), 0.0)]

     | ECnotin(n, e) ->
             if name_in_atom n atom then
                 let p = eval_ef e evmap atom in
                   if p=zero_poly then
                       []
                   else
                    [Le(p, 0.0)]
             else
                 []
      | ECfn(e, names) ->
              if atom_sub_names atom names then
                 []
              else
                 let p = eval_ef e evmap atom in
                   if p=zero_poly then
                       []
                   else
                    [Le(p, 0.0)]

let rec msg_subst m ind n =
  match m with
     Name(ENname(_)) -> m
   | Name(ENindex(i)) -> if i=ind then Name(ENname(n)) else m
   | Unit -> Unit
   | Pair(m1,m2) -> Pair(msg_subst m1 ind n, msg_subst m2 ind n)
   | EncSym(m1,m2) -> EncSym(msg_subst m1 ind n, msg_subst m2 ind n)
   | EncAsym(m1,m2) -> EncAsym(msg_subst m1 ind n, msg_subst m2 ind n)
   | Inl(m1) -> Inl(msg_subst m1 ind n)
   | Inr(m1) -> Inr(msg_subst m1 ind n)
let atom_subst x ind n =
  match x with
    AEend(m) -> AEend(msg_subst m ind n)
  | AEchk(l,ENname(_),e) -> x
  | AEchk(l,ENindex(i),e) -> if i=ind then AEchk(l,ENname(n),e) else x


let rec efsub emap e =
  match e with
    Evar v -> Emap(try List.assoc v emap with Not_found -> [])
  | Emap _ -> e
  | Eplus(e1,e2) ->
        let e1' = efsub emap e1 in
        let e2' = efsub emap e2 in
        ( match (e1', e2') with
           (Emap l1, Emap l2) ->
              let l = merge compare l1 l2 in
                Emap(delete_duplication2 (fun (x,_)->fun (y,_)->compare x y)
                                    (fun (x,r1)->fun (y,r2)->(x,r1+.r2)) l)
         | _ -> raise (Fatal "efsub")
        )
  | Esub(ind,n,e1) ->
      let e' = efsub emap e1 in
       (match e' with
          Emap(l1) ->
            let l1' = List.map (fun (x, r) -> (atom_subst x ind n, r)) l1 in
            let l1'' = List.sort compare l1' in
                Emap(delete_duplication2 (fun (x,_)->fun (y,_)->compare x y)
                                    (fun (x,r1)->fun (y,r2)->(x,r1+.r2)) l1'')
        | _ ->  raise (Fatal "efsub")
       )

let rec check_leq_emap l1 l2 atoms =
  match l1 with
    [] -> ()
  | (a,x)::l1' ->
      if (List.mem a atoms)|| x=0.0 
      then check_leq_emap l1' l2 atoms
      else
        try
          let y = List.assoc a l2 in
          if x<=y then check_leq_emap l1' l2 atoms
          else raise Unsatisfiable
        with
          Not_found -> raise Unsatisfiable
        
let check_eq_emap l1 l2 atoms =
  (check_leq_emap l1 l2 atoms; check_leq_emap l2 l1 atoms)

let check_eca eca atoms =
  match eca with
    ECeq(e1,e2) ->
      let e1' = efsub [] e1 in
      let e2' = efsub [] e2 in
        (match (e1',e2') with
           (Emap(l1), Emap(l2)) -> check_eq_emap l1 l2 atoms
         | _ -> raise (Fatal "check_eca")
         )
  | ECsub(e1,e2) ->
      let e1' = efsub [] e1 in
      let e2' = efsub [] e2 in
        (match (e1',e2') with
           (Emap(l1), Emap(l2)) -> check_leq_emap l1 l2 atoms
         | _ -> raise (Fatal "check_eca")
         )
  | _ -> ()

let eca2lc eca (evmap: (eid * (atomic_effect * ovarid) list) list) =
   let evs = get_efvars_from_eca eca in
   let atoms = 
       List.fold_left 
         (fun ats -> fun ev -> 
              merge_and_unify compare ats (List.map fst (List.assoc ev evmap)))
         []
         evs in
   let lc = List.flatten (List.map
                      (eca2lc_atom eca evmap) atoms) in
   let _ = check_eca eca atoms in
      lc
(***
 *** ec2lc:  ef_constraints -evmap -atoms -linear_constraints
 ***)

let ec2lc_aux ec evmap  =
   List.flatten (List.map
                      (fun eca ->eca2lc eca evmap) ec)


let rec positive_ef efc =
 List.map (fun (a, ov) -> Le(P([(ov,-1.0)], 0.0), 0.0)) efc

let rec positive_evmap evmap =
 List.flatten(List.map (fun (v, efc) -> positive_ef efc) evmap)

let rec top_evs e =
  match e with
    Evar(n) -> [n]
  | Eplus(e1,e2) ->
     let evs1 = top_evs e1 in
     let evs2 = top_evs e2 in
       merge_and_unify compare evs1 evs2
  | Esub(_,_,e1) ->
      top_evs e1
  | Emap _ -> []

let zero_ev_in_eac eac =
  match eac with
    ECeq(e1, Emap[]) -> top_evs(e1)
  | ECeq(Emap[], e1) -> top_evs(e1)
  | ECsub(e1, Emap[]) -> top_evs(e1)
  | ECfn(e1, []) -> top_evs(e1)
  | _ -> []

let rec zero_ev ec =
  match ec with
    [] -> []
  | eac::ec' ->
      let zevs1 = zero_ev_in_eac eac in
      let zevs2 = zero_ev ec' in
        merge_and_unify compare zevs1 zevs2

let eplus e1 e2 =
  if e1=Emap[] then e2
  else if e2=Emap[] then e1 else Eplus(e1,e2)

let rec substzero_ef zeros e =
  match e with
    Evar(n) -> 
       if List.mem n zeros then Emap[] else e
  | Eplus(e1,e2) ->
      let e1' = substzero_ef zeros e1 in
      let e2' = substzero_ef zeros e2 in
           eplus e1' e2'
  | Esub(i,n,e1) ->
      let e1' = substzero_ef zeros e1 in
	if e1' = Emap([]) then e1'
	else Esub(i,n,e1')
  | Emap _ -> e

(** 
 ** get_substitutions:
 **       ef_constraints ->substitutions
 **)


let substzero_eac zeros eac =
  match eac with
    ECeq(e1,e2) ->
      let e1' = substzero_ef zeros e1 in
      let e2' = substzero_ef zeros e2 in
        if e1'=Emap[]&& e2' = Emap[]
        then []
        else [ECeq(e1',e2')]
  | ECsub(e1,e2) ->
      let e1' = substzero_ef zeros e1 in
      let e2' = substzero_ef zeros e2 in
        if e1'=Emap[]
        then []
        else [ECsub(e1',e2')]
  | ECnotin(name,e1) ->
      let e1' = substzero_ef zeros e1 in
        if e1'=Emap[]
        then []
        else [ECnotin(name,e1')]
  | ECfn(e1, names) ->
      let e1' = substzero_ef zeros e1 in
        if e1'=Emap[]
        then []
        else [ECfn(e1', names)]
      
let rec substzero_ec zeros ec =
  match ec with
    [] -> []
  | eac::ec' ->
      let ec1 = substzero_eac zeros eac in
      let ec2 = substzero_ec zeros ec' in
        ec1@ec2

let rec simplify_ec c =
  let zeros = zero_ev c in
  let c' = substzero_ec zeros c in
    if List.length c = List.length c' 
    then c'
    else simplify_ec c'

let unconstrained_atom_by_eca ev anames eca =
  match eca with
    ECnotin(name, Evar(n)) ->
      not((n=ev) && (List.mem name anames))
  | ECfn(Evar(n), names) ->
      if n=ev then
         List.for_all (fun x -> List.mem x names) anames
      else
         true
  | _ -> true

let rec unconstrained_atom ev anames ec =
  match ec with
    [] -> true
  | eca::ec' ->
       (unconstrained_atom_by_eca ev anames eca)
      && (unconstrained_atom ev anames ec')

let filter_atoms ec (ev, l) =
  (ev, List.filter (fun (atom, _) -> unconstrained_atom ev (names_of_atom atom) ec) l)

let filter_atoms_from_evdom ec ev atoms = 
  List.filter (fun atom -> unconstrained_atom ev (names_of_atom atom) ec) atoms

let merge_evc evc0 evc1 =
  let evc = merge_and_unify compare evc0 evc1 in
   (delete_duplication2
      (fun (x,_) -> fun(y,_) -> compare x y)
      (fun (x1,l1) -> fun(x2,l2) -> (x1, l1@l2))
      evc)

let merge_evdom evdom0 evdom1 =
  let evdom = merge_and_unify compare evdom0 evdom1 in
   (delete_duplication2
      (fun (x,_) -> fun(y,_) -> compare x y)
      (fun (x1,l1) -> fun(x2,l2) -> (x1, merge_and_unify compare l1 l2))
      evdom)

let rec mk_evc c =
  match c with 
   [] -> []
  | ac::c' ->
     let evc0 = mk_evc_ac ac in
     let evc1 = mk_evc c' in
       merge_evc evc0 evc1
and mk_evc_ac ac =
  match ac with
     ECeq(e1,e2) -> mk_evc [ECsub(e1,e2); ECsub(e2,e1)]
   | ECsub(e1,e2) ->
       let evs = get_efvars_from_ef e1 in
         if evs=[]
         then [(-1, [(e1,e2)])]
         else
           List.map (fun ev -> (ev, [(e1,e2)])) evs
   | _ -> []

let rec doms_of_ef e evindex tab: atomic_effect list =
  match e with
    Emap m -> (List.map fst m)
  | Evar ev -> (try tab.(Hashtbl.find evindex ev) 
               with Not_found -> [])
  | Eplus(e1,e2) ->
        merge_and_unify compare (doms_of_ef e1 evindex tab)
                                (doms_of_ef e2 evindex tab)
  | Esub(i, n, e1) ->
        let atoms = doms_of_ef e1 evindex tab in
        let atoms' = expand_atoms [(i,n)] atoms 
              (*** TO DO: expand_atom_by_as may generate irrelevant atoms ***)
        in atoms'

let rec rev_doms_of_ef e atoms =
  match e with
    Emap m -> []
  | Evar ev -> [(ev, atoms)]
  | Eplus(e1,e2) ->
        let evdom1 = rev_doms_of_ef e1 atoms in
        let evdom2 = rev_doms_of_ef e2 atoms in
           merge_evdom evdom1 evdom2           
  | Esub(i, n, e1) ->
        let atoms' = expand_atoms [(i,n)] atoms in
         rev_doms_of_ef e1 atoms';;

let rec update_tab tab evindex l c =
  match l with
    [] -> []
  | (e1,e2)::l' ->  (* expand the domain of effect variables in e2 so that dom(e1) \subseteq dom(e2) *)
     let atoms = doms_of_ef e1 evindex tab in
     let evdom1 = rev_doms_of_ef e2 atoms in
     let evars1 =
      List.fold_left 
        (function evs -> function (ev, atoms1) ->
                  let atoms2 = filter_atoms_from_evdom c ev atoms1 in
                  let i = Hashtbl.find evindex ev in
                  let old_atoms = tab.(i) in
                  let atoms' = 
                    merge_and_unify compare atoms2 old_atoms in
                    if List.length old_atoms = List.length atoms' then
                       evs
                    else
                       (tab.(i) <- atoms'; 
                        merge_and_unify compare [ev] evs)
        )
        []
        evdom1 in
     let evars2 = update_tab tab evindex l' c in
       merge_and_unify compare evars1 evars2

let rec iter_expand_evdom (tab: (atomic_effect list) array) evindex evc evars c =
  match evars with
    [] -> ()
  | ev::evars' ->
     let evars1 = 
           try update_tab tab evindex (List.assoc ev evc) c
           with Not_found -> []
     in
     let evars'' = merge_and_unify compare evars1 evars' 
     in
      iter_expand_evdom tab evindex evc evars'' c

let mk_evdom c evars =
  let evc = mk_evc c in
  let r = ref 0 in
  let evindex = Hashtbl.create 1000 in
  let _ = 
               List.map (function ev -> 
                          let n= !r in (r:=!r+1; Hashtbl.add evindex ev n))
                        evars 
  in
  let tab = Array.make !r [] in
  let c1 = List.filter (fun ac -> match ac with ECnotin _ -> true | ECfn _ -> true | _ -> false) c in
  let _ = iter_expand_evdom tab evindex evc ((-1)::evars) c1 in
    List.map (fun ev -> (ev, tab.(Hashtbl.find evindex ev))) evars

let evdom2evmap evdom =
  List.map (fun (ev, atoms) -> mk_evsubst_for_each_efvar atoms ev) evdom

let rec get_eqevc c (eqev, r)=
  match c with
    [] -> (eqev, r)
  | ac::c' ->
     match ac with
       ECeq(Evar(m), Evar(n)) -> 
          get_eqevc c' ((m,n)::eqev, r)
    | _ ->
          get_eqevc c' (eqev, ac::r)

let rec solve_eqev eqev renaming =
  let lookup n = try List.assoc n renaming with Not_found -> n 
  in
  let extend_renaming m n =
       let renaming' = 
         List.map (fun (x,y) -> (x, if m=y then n else y)) renaming 
       in (m,n)::renaming'
  in
    match eqev with
      [] -> renaming
    | (m,n)::eqev' ->
         let m' = lookup m in
         let n' = lookup n in
          if m'=n' then solve_eqev eqev' renaming
          else
            let renaming' = extend_renaming m' n' in
            solve_eqev eqev' renaming'

(***+++++++++++++++++++for the eVar in the Echk<n,eVar>++++++++++++++++++***)

let rec rename_ev_in_atomicef renaming ae =
  let rename_ev_in_atomicef1 renaming m =
     match m with
      Evar(x) -> (try Evar(List.assoc x renaming) with 
                 Not_found -> m)  
    | _ -> m in
  let rename_ev_in_atomicef2 renaming y =
     match y with
       AEend(m) -> AEend(m)
     | AEchk(l,a,e) ->AEchk(l,a,rename_ev_in_atomicef1 renaming e) in
    match ae with
       []->[]
     | (a,b)::res -> 
        [(rename_ev_in_atomicef2 renaming a,b)]@(rename_ev_in_atomicef renaming res)

(***+++++++++++++++++++++++++++++++++++++***)



let rec rename_ev_in_ef renaming e =
  match e with
    Emap(x) -> Emap(rename_ev_in_atomicef renaming x)
  | Evar(x) -> (try Evar(List.assoc x renaming) with 
                 Not_found -> e)
  | Eplus(e1,e2) ->
       Eplus(rename_ev_in_ef renaming e1, rename_ev_in_ef renaming e2)
  | Esub(i,n,e) -> 
       Esub(i,n, rename_ev_in_ef renaming e)

let rename_ev_in_ac renaming ac =
  match ac with
    ECeq(e1,e2) -> ECeq(rename_ev_in_ef renaming e1, rename_ev_in_ef renaming e2)
  | ECsub(e1,e2) -> ECsub(rename_ev_in_ef renaming e1, rename_ev_in_ef renaming e2)
  | ECnotin(x, e) -> ECnotin(x, rename_ev_in_ef renaming e)
  | ECfn(e, names) -> ECfn(rename_ev_in_ef renaming e, names)

let rename_ev_in_c renaming c =
  List.map (rename_ev_in_ac renaming) c




let ec2lc c =
  let _ = let evars = get_efvars c in
             print_string ("# of effect variables: "
                 ^(string_of_int (List.length evars))^"\n") in
  let _ = (print_string ("2.0: "^(string_of_float(Sys.time()))^"\n"); flush stdout) in
  let c1 = simplify_ec c in
  let _ = (print_string ("2.1: "^(string_of_float(Sys.time()))^"\n"); flush stdout) in
  let (eqev, c2) = get_eqevc c1 ([], []) in
  let ev_renaming = solve_eqev eqev [] in
  let _ = (print_string ("2.2: "^(string_of_float(Sys.time()))^"\n"); flush stdout) in
  let c3 = rename_ev_in_c ev_renaming c2 in
  let evars = get_efvars c3 in
  (*** let atoms = get_allatoms c' in ***)
  let _ = print_string ("# of effect constr. (after simplification): "
                 ^(string_of_int (List.length c3))^"\n") in
  let _ = (print_string ("2.3: "^(string_of_float(Sys.time()))^"\n"); flush stdout) in
  let evdom = mk_evdom c3 evars in
  let _ = (print_string ("2.4: "^(string_of_float(Sys.time()))^"\n"); flush stdout) in
  let evmap = evdom2evmap evdom in
  let _ = (print_string ("2.5: "^(string_of_float(Sys.time()))^"\n"); flush stdout) in
(**   let evmap' = List.rev_map (filter_atoms c3) evmap in **)
  let evmap' = evmap in
  let _ = (print_string ("2.6: "^(string_of_float(Sys.time()))^"\n"); flush stdout) in
  let lc1' = ec2lc_aux c3 evmap' in
  let _ = (print_string ("2.7: "^(string_of_float(Sys.time()))^"\n"); flush stdout) in
  let lc1 = List.rev_map normalize_ineq lc1' in
  let _ = (print_string ("2.8: "^(string_of_float(Sys.time()))^"\n"); flush stdout) in
  let vars = List.flatten (List.map (fun (ev, l) -> List.map snd l) evmap') in
  let _ = (print_string ("2.9: "^(string_of_float(Sys.time()))^"\n"); flush stdout) in
  let evmap2 = 
        List.map 
          (fun (x,y) -> 
             (x, try List.assoc y evmap' with Not_found -> [])) ev_renaming in
     (lc1, evmap'@evmap2, vars)



 


let lookup_solution (imap, array) v =
  try 
    let i=List.assoc v imap in
      array.(i)
  with
    Not_found -> 0.0

let compute_ev evmap vars solution =
  let rec iter evmap index =
    match evmap with
       [] -> []
     | (ev, l)::evmap' -> 
          let n = List.length l in
          let new_evmap = iter evmap' (index+n) in
(***          let indices = fromto index (index+n) in 
 ***          let new_l = List.map (fun ((a, v), i) -> (a, solution.(i))) 
 ***                               (List.combine l indices) 
 ***)
          let new_l = List.map (fun (a,v) -> (a, lookup_solution solution v)) l
          in
             (ev, new_l)::new_evmap
  in
  let evmap1 = iter evmap 0 in
     List.map (fun (ev,l) -> (ev, List.filter (fun (a,r)->r>0.0) l)) evmap1


