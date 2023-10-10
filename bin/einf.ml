
open Datatype
open Utilities


exception TypeError of string
exception TODO
exception Teq of etype * etype
exception PubWrong of etype

type et_env = (name * etype) list
let one = 1.
let zero = 0.

let ef_zero = Emap([])
let ef_check l en ef = Emap [(AEchk(l,en,ef), one)]
let ef_end m = Emap [(AEend(m), one)]
let unT = ETName(Pub,ef_zero,ef_zero)

let eplus(e1, e2) =
  if e1=ef_zero then e2
  else if e2=ef_zero then e1
  else Eplus(e1,e2)

let current_evid = ref 0;;
let fresh_evid() =
  (current_evid := !current_evid + 1;
   !current_evid);;



let rec teq t1 t2 =    
  if (t1=t2 || t1=ETany || t2=ETany) then []
  else match (t1,t2) with
    (ETName(_,e1,e2),ETName(_,e1',e2')) ->[ECeq(e1,e1')]@ [ECeq(e2,e2')]
  | (ETSKey(t1),ETSKey(t2)) -> teq t1 t2
  | (ETChan(t1),ETChan(t2)) -> teq t1 t2
  | (ETEKey(t1),ETEKey(t2)) -> teq t1 t2
  | (ETDKey(t1),ETDKey(t2)) -> teq t1 t2
  | (ETPair(t1,t2),ETPair(t1',t2')) -> (teq t1 t1') @ (teq t2 t2')
  | (ETVari(t1,t2),ETVari(t1',t2')) -> (teq t1 t1') @ (teq t2 t2')
  | _ -> raise (Teq (t1, t2)) 

(***  | _ -> raise (Fatal "teq") ***)

let rec tpub ty = 
  let rec ttainted2 ty2 = match ty2 with
      ETUnit -> []
    | ETName(l,e1,e2) -> 
             if l=Pub then [ECsub(e2,Emap([]))]
             else []
    | ETSKey(t) -> (tpub t)@(ttainted2 t)
    | ETChan(t) -> raise (TypeError "tpub")
    | ETEKey(t) -> (tpub t)
    | ETDKey(t) -> (ttainted2 t)
    | ETPair(t1,t2) -> (ttainted2 t1)@(ttainted2 t2)
    | ETVari(t1,t2) -> (ttainted2 t1)@(ttainted2 t2)
    | ETany -> []  in 
 match ty with
    ETUnit -> []
  | ETName(Pub,e1,e2) -> [ECsub(e1,Emap([]))]
  | ETChan(t) -> raise (TypeError "tpub")
  | ETName(Pr,e1,e2) -> raise (PubWrong (ty))
  | ETSKey(t) -> (tpub t)@(ttainted2 t)
  | ETEKey(t) -> (ttainted2 t)
  | ETDKey(t) -> (tpub t)
  | ETPair(t1,t2) -> (tpub t1)@(tpub t2)
  | ETVari(t1,t2) -> (tpub t1)@(tpub t2)
  | ETany -> []

let rec ttainted ty = 
 let rec tpub2 ty2 = 
   match ty2 with
      ETUnit -> []
    | ETChan(t) -> raise (TypeError "tpub")
    | ETName(Pub,e1,e2) -> [ECsub(e1,Emap([]))]
    | ETName(Pr,e1,e2) ->  raise (PubWrong (ty))
    | ETSKey(t) -> (tpub2 t)@(ttainted t)
    | ETEKey(t) -> (ttainted t)
    | ETDKey(t) -> (tpub2 t)
    | ETPair(t1,t2) -> (tpub2 t1)@(tpub2 t2)
    | ETVari(t1,t2) -> (tpub2 t1)@(tpub2 t2)
    | ETany -> []  in
 match ty with
    ETUnit -> []
  | ETChan(t) -> raise (TypeError "tpub")
  | ETName(l,e1,e2) -> 
         if l=Pub then [ECsub(e2,Emap([]))]
         else []
  | ETSKey(t) -> (tpub2 t)@(ttainted t)
  | ETEKey(t) -> (tpub2 t)
  | ETDKey(t) -> (ttainted t)
  | ETVari(t1,t2) -> (ttainted t1)@(ttainted t2)
  | ETPair(t1,t2) -> (ttainted t1)@(ttainted t2)
  | ETany -> []


(*******
let rec genT ty =
  match ty with
    ETName(_) -> []
  | ETKey(_) -> []
  | _ -> raise (TypeError "genT")  ********)


let shift_name n =
  match n with
    ENname(_) -> n
  | ENindex(i) -> ENindex(i+1)

let shift_names ns =
  List.map shift_name ns

let rec wfT ty ns = 
  match ty with
    ETUnit -> []
  | ETName(l,e1,e2) -> [ECfn(e1, ns)]@[ECfn(e2,ns)]
  | ETSKey(t) -> wfT t ns
  | ETEKey(t) -> wfT t ns 
  | ETDKey(t) -> wfT t ns
  | ETPair(t1,t2) -> 
       let ec1 = (wfT t1 ns) in
       let ns' = [ENindex(0)]@ (shift_names ns) in
       let ec2 = wfT t2 ns' in
         ec1@ec2
  | ETVari(t1,t2) -> (wfT t1 ns)@(wfT t2 ns)
  | ETChan(t) -> wfT t ns
  | ETany -> []

let wfE e ns = [ECfn(e, ns)]

let name2exname n = ENname n
let dom env = (List.map name2exname (List.map fst env))

let rec sty2ety sty =
  match sty with
    TUnit -> ETUnit
  | TName(l) -> ETName(l,Evar(fresh_evid()),Evar(fresh_evid()))
  | TPair(t1,t2) -> ETPair(sty2ety t1, sty2ety t2)
  | TVari(t1,t2) -> ETVari(sty2ety t1, sty2ety t2)
  | TSKey(t) -> ETSKey(sty2ety t)
  | TEKey(t) -> ETEKey(sty2ety t)
  | TDKey(t) -> ETDKey(sty2ety t) 
  | TChan(t) -> ETChan(sty2ety t)
  | TVar(_) -> ETName(Pr,Evar(fresh_evid()),Evar(fresh_evid()))


let stenv2etenv stenv =
  List.map 
  (fun (n, st) -> (match n with ENname(m) -> (m, sty2ety st) | _ -> raise (Fatal "stenv2etenv")))
  stenv

let rec ef_subst e n ind =
  Esub(ind, n, e)

let rec et_subst t n ind =
  match t with
    ETUnit -> ETUnit
  | ETName(l,e1,e2) -> ETName(l,ef_subst e1 n ind,ef_subst e2 n ind)
  | ETPair(t1,t2) -> ETPair(et_subst t1 n ind, et_subst t2 n (ind+1))
  | ETVari(t1,t2) -> ETVari(et_subst t1 n ind, et_subst t2 n ind)
  | ETChan(t1) -> ETChan(et_subst t1 n ind)
  | ETSKey(t1) -> ETSKey(et_subst t1 n ind)
  | ETEKey(t1) -> ETEKey(et_subst t1 n ind)
  | ETDKey(t1) -> ETDKey(et_subst t1 n ind)
  | ETany -> ETany

let rec imitate_etype t =
  match t with
    ETUnit -> ETUnit
  | ETName(l,e1,e2) -> ETName(l,Evar(fresh_evid()),Evar(fresh_evid()))
  | ETPair(t1,t2) -> ETPair(imitate_etype t1, imitate_etype t2)
  | ETVari(t1,t2) -> ETVari(imitate_etype t1, imitate_etype t2)
  | ETSKey(t1) -> ETSKey(imitate_etype t1)
  | ETEKey(t1) -> ETEKey(imitate_etype t1)
  | ETChan(t1) -> ETChan(imitate_etype t1)
  | ETDKey(t1) -> ETDKey(imitate_etype t1)
  | ETany -> ETany

let rec msg_inf (env: et_env) (m: message): effect * etype * ef_constraint =
  match m with
    Name(ENname n) ->
      let t1 = try List.assoc n env with Not_found -> raise (Fatal (n^" is undefined")) in
        (match t1 with
          ETName(l,ef1,ef2) ->
              let evid1 = fresh_evid() in
              let evid2 = fresh_evid() in
              let evid3 = fresh_evid() in 
              let ef1' = Evar(evid1) in
              let ef2' = Evar(evid2) in
              let ef3' = Evar(evid3) in
              let t = ETName (l,ef1',Eplus(ef2, ef2')) in
              let ce = [ECeq(ef1,Eplus(ef1',ef3'))] in
                (Eplus(ef3',ef2'), t, ce)
        | _ -> (ef_zero, t1, [])
        )
  | Name _ -> raise (Fatal "msg_inf")
  | Unit -> (ef_zero, ETUnit, [])
  | Pair(m1,m2) ->
     let (ef1,t1,ec1) = msg_inf env m1 in
     let (ef2,t2,ec2) = msg_inf env m2 in
       (match m1 with
         Name(ENname n) ->
            let t2' = imitate_etype t2 in
            let t2'' = et_subst t2' n 0 in
              (eplus(ef1,ef2), ETPair(t1,t2'), ec1@ec2@(teq t2 t2''))
       | _ -> (eplus(ef1,ef2), ETPair(t1,t2), ec1@ec2)
        ) 
  | Inl(m1) -> 
     let (ef1,t1,ec1) = msg_inf env m1 in
       (ef1, ETVari(t1, ETany), ec1)
  | Inr(m1) -> 
     let (ef1,t1,ec1) = msg_inf env m1 in
       (ef1, ETVari(ETany, t1), ec1)
  | EncSym(m1,m2) ->
     let (ef1,t1,ec1) = msg_inf env m1 in
     let (ef2,t2,ec2) = msg_inf env m2 in
       ( match t2 with
            ETSKey(t0) ->
               (eplus(ef1,ef2), unT,[ECeq(ef2,Emap([]))]@(teq t0 t1)@ec1@ec2)
          | _ -> raise (TypeError "msg_inf")
       )

  | EncAsym(m1,m2) ->
     let (ef1,t1,ec1) = msg_inf env m1 in
     let (ef2,t2,ec2) = msg_inf env m2 in
       ( match t2 with
            ETEKey(t0) ->
               (eplus(ef1,ef2), unT,[ECeq(ef2,Emap([]))]@(teq t0 t1)@ec1@ec2)
          | _ -> raise (TypeError "msg_inf")
       )
    


(*** etype_inf: et_env -> stype procexp -> effect * ef_constraint ***)
let rec etype_inf (env: et_env) (p: stype procexp) = 
 match p with
    Zero -> (ef_zero,[], Zero)
  | Out(m,n) ->
      let (ef_m,ty_m,_) = msg_inf env m in
      let (ef_n,ty_n,ec_n) = msg_inf env n in
      let ec1 = (teq ty_m unT) @ (tpub ty_n) in
	(ef_n, ec_n@ec1, Out(m,n))
  | OutS(m,n) ->
      let (ef_m,ty_m,_) = msg_inf env m in
      let (ef_n,ty_n,ec_n) = msg_inf env n in
      let ec1 = (teq ty_m (ETChan(ty_n))) in
      (***  let ec2 = [ECeq(ef_m,Emap([]))] in ***)
	(ef_n, ec_n@ec1, OutS(m,n))
  | In(m,y,sty,pr) ->
      let (ef_m,ty_m,_) = msg_inf env m in
      let ty_n = sty2ety sty in
      let env' = env_extend y ty_n env in
      let (ef,ec0, pr') = etype_inf env' pr in
      let ec1 = (teq ty_m unT) @ (ttainted ty_n) in
      let ec2 = [ECnotin(ENname y,ef)] in
      let ec3 = wfT ty_n (dom env) in
	(ef, ec0@ec1@ec2@ec3, In(m,y,ty_n,pr'))
  | InS(m,y,sty,pr) ->
      let (ef_m,ty_m,_) = msg_inf env m in
      let ty_n = sty2ety sty in
      let env' = env_extend y ty_n env in
      let (ef,ec0, pr') = etype_inf env' pr in
      let ec1 = (teq ty_m (ETChan(ty_n))) in
      let ec2 = [ECnotin(ENname y,ef)] in
      let ec3 = wfT ty_n (dom env) in
	(ef, ec0@ec1@ec2@ec3, InS(m,y,ty_n,pr'))

  | Par(pr1,pr2) ->
      let (ef1,ec1, pr1') = etype_inf env pr1 in
      let (ef2,ec2, pr2') = etype_inf env pr2 in
	(Eplus(ef1,ef2),ec1 @ ec2, Par(pr1',pr2'))
  | Copy(pr) ->
       let (ef_zero,ec, pr') = etype_inf env pr in
        (ef_zero,ec,Copy(pr'))
  | Nu(x,sty,pr) -> 
      let ty_x = sty2ety sty in
       (match ty_x with
         | ETName(l,e1,e2) ->
           let env' = env_extend x ty_x env in
           let (ef,ec, pr') = etype_inf env' pr in
           let ro = fresh_evid () in
           let ec1 = (wfT ty_x (dom  env)) @ (wfE (Evar(ro)) (dom env))in
           let ec2 = [ECsub(ef, Eplus(Evar(ro), ef_check l (ENname(x)) e1));
                       ECsub(e2,ef_zero);ECnotin(ENname x,Evar(ro))] in
	        (Evar(ro),ec @ ec1@ec2, Nu(x, ty_x, pr'))
         | _ -> raise (TypeError "etype_inf")
        )
  | NuS(x,sty,pr) -> 
      let ty_x = sty2ety sty in
      let env' = env_extend x ty_x env in
      let (ef,ec, pr') = etype_inf env' pr in
      let ro = fresh_evid () in
      let ec1 = (wfT ty_x (dom  env)) @ (wfE (Evar(ro)) (dom env))in
      let ec2 = [ECsub(ef,Evar(ro));ECnotin(ENname x,Evar(ro))] in
	(Evar(ro),ec @ ec1@ec2, NuS(x, ty_x, pr'))

  | NuSym(x,sty,pr) -> 
      let ty_x = sty2ety sty in
      let env' = env_extend x ty_x env in
      let (ef,ec, pr') = etype_inf env' pr in
      let ro = fresh_evid () in
      let ec1 = (wfT ty_x (dom  env)) @ (wfE (Evar(ro)) (dom env))in
      let ec2 = [ECnotin(ENname x,Evar(ro))]@[ECsub(ef,Evar(ro))] in
	(Evar(ro),ec @ ec1@ec2, NuSym(x, ty_x, pr'))
   | NuAsym(x,stx,y,sty,pr) -> 
      let ty_x = sty2ety stx in
      let ty_y = sty2ety sty in
      let env' = env_extend x ty_x env in
      let env'' = env_extend y ty_y env' in
      let (ef,ec, pr') = etype_inf env'' pr in
      (match (ty_x,ty_y) with
	| (ETEKey(tx) , ETDKey(ty)) ->
           let ro = fresh_evid () in
           let ec1 = (wfT ty_x (dom  env)) @ (wfT ty_y (dom  env)) 
                            @ (wfE (Evar(ro)) (dom env)) @ (teq tx ty )in
           let ec2 = [ECsub(ef, Evar(ro));ECnotin(ENname x,Evar(ro));
                      ECnotin(ENname y,Evar(ro))] in
	       (Evar(ro),ec @ ec1@ec2, NuAsym(x, ty_x, y, ty_y, pr'))
         
        | _ -> raise (TypeError "etype_inf")
      )

  | Check(m,n,pr) ->
      let em = ENname(m) in
      let en = ENname(n) in
      let (ef_m,ty_m,ec_m) = msg_inf env (Name(em)) in
      let (ef_n,ty_n,ec_n) = msg_inf env (Name(en)) in
      (match (ty_m,ty_n) with
        | (ETName(l1,e1,e2),ETName(l2,e1',e2')) ->
          if l1 = l2 then
          let (ef_p,ec_p, pr') = etype_inf env pr in
          let ef = Emap([]) in
          let ro = fresh_evid () in  (*** eo in Chk ***)
          let r1 = fresh_evid () in  (*** e ***)
          let ec_e = [ECeq(e1',ef);ECsub(ef_n,ef_zero); ECsub(ef_m,ef_zero)] 
                       @ [ECsub(ef_p,Eplus(Evar(r1),Eplus(Evar(ro),e2')))]
                       @[ECeq(Evar(ro),e1)] in
                 (Eplus(Evar(r1),ef_check l1 em (Evar(ro))),ec_p @ ec_m @ ec_n  
                   @ ec_e, Check(m,n,pr'))
          else raise (PubWrong(ty_m))
        | _ -> raise (TypeError "etype_inf")

      )
  | Case(m,y,sty1,pr1,z,sty2,pr2) ->
      let (ef_m,ty_m,ec_m) = msg_inf env m in
      let ty_y = sty2ety sty1 in
      let env1 = env_extend y ty_y env in
      let ty_z = sty2ety sty2 in
      let env2 = env_extend z ty_z env in
      let (ef1,ec1,pr1') = etype_inf env1 pr1 in
      let (ef2,ec2,pr2') = etype_inf env2 pr2 in
      let ro = fresh_evid () in
      let ef = Evar(ro) in
      let ec_t = (teq ty_m (ETVari(ty_y,ty_z)))@(wfT ty_y (dom env))@(wfT ty_z (dom env)) in
      let ec_e = [ECsub(ef1,ef); ECsub(ef2,ef);ECnotin(ENname y,ef);ECnotin(ENname z,ef)] in
	(Evar(ro),ec1 @ ec2 @ ec_m @ ec_t @ ec_e, Case(m,y,ty_y,pr1',z,ty_z,pr2'))
  | DecSym(m,y,sty, k,pr) ->

      let (ef_m,ty_m,ec_m) = msg_inf env m in
      let (ef_k,ty_k,ec_k) = msg_inf env k in
      let ty_y = sty2ety sty in
      let env' = env_extend y ty_y env in
      let (ef,ec, pr') = etype_inf env' pr in
      let ec_t = (teq ty_m unT) @ (teq ty_k (ETSKey(ty_y)))@(wfT ty_y (dom env))in
      let ec_e = [ECsub(ef_m,ef_zero);ECeq(ef_k,ef_zero);ECnotin(ENname y,ef)] in
	(ef,ec @ ec_m @ ec_k @ ec_t @ ec_e, DecSym(m,y,ty_y,k,pr'))
 
   | DecAsym(m,y,sty, k,pr) ->
      let (ef_m,ty_m,ec_m) = msg_inf env m in
      let (ef_k,ty_k,ec_k) = msg_inf env k in
      let ty_y = sty2ety sty in
      let env' = env_extend y ty_y env in
      let (ef,ec, pr') = etype_inf env' pr in
      let ec_t = (teq ty_m unT) @ (teq ty_k (ETDKey(ty_y)))@(wfT ty_y (dom env))in
      let ec_e = [ECsub(ef_m,ef_zero);ECeq(ef_k,ef_zero);ECnotin(ENname y,ef)] in
	(ef,ec @ ec_m @ ec_k @ ec_t @ ec_e, DecAsym(m,y,ty_y,k,pr'))

  | Split(m,y,sty1,z,sty2,pr) ->
      let (ef_m,ty_m,ec_m) = msg_inf env m in
      let ty_y = sty2ety sty1 in
      let ty_z = sty2ety sty2 in
      let ty_z' = et_subst ty_z y 0 in
      let env' = env_extend y ty_y env in
      let env'' = env_extend z ty_z' env' in
      let (ef,ec, pr') = etype_inf env'' pr in
      let ec_t = teq ty_m (ETPair(ty_y,ty_z)) in
      let ec_e = [ECnotin(ENname y,ef);ECnotin(ENname z,ef)] in
	(ef,ec @ ec_m @ ec_t @ ec_e, Split(m,y,ty_y,z,ty_z',pr'))

  | Match(m,a,y,sty,pr) ->
      let (ef_m,ty_m,ec_m) = msg_inf env m in
      let (ef_a,ty_a,ec_a) = msg_inf env (Name(ENname a)) in
      let ty_y = sty2ety sty in
      let ty_y' = et_subst ty_y a 0 in		
      let env' = env_extend y ty_y' env in
      let (ef,ec, pr') = etype_inf env' pr in
      let ec_t = teq ty_m (ETPair(ty_a,ty_y)) in
      let ec_e = [ECnotin(ENname y,ef)] in
	(ef,ec @ ec_m @ ec_t @ ec_e @ ec_a , Match(m,a,y,ty_y',pr'))

  | Begin(m,pr) -> 
      let (ef,ec,pr') = etype_inf env pr in
      let ro = fresh_evid () in
      let ec_e = [ECsub(ef, Eplus(Evar(ro), ef_end(m)))] in
	(Evar(ro),ec @ ec_e, Begin(m,pr'))
  | End(m) ->
	( ef_end(m),[], End(m))

     

let einf stenv p =
  let etenv = stenv2etenv stenv in
  let (ef, ec1, p1) = etype_inf etenv p in
  let ec2 = List.flatten (List.map (fun (x,t)->ttainted t) etenv) in
  let ec3 = [ECsub(ef,ef_zero)] in
    (ec3@ec2@ec1, p1)


