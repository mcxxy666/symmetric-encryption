
open Datatype


(*** type environment ***)
type 'a env = (ex_name * 'a) list

let rec env_lookup x env = match env with
    [] -> raise Not_found
  | (x',ty')::tl -> if x=x' then ty' else (env_lookup x tl)

let env_extend x ty env = (x,ty)::env



let env_map f env = List.map (fun (x,v) -> (x,f v)) env

let rec env_dom env = match env with
    [] -> []
  | (x,_)::tl -> x::(env_dom tl)

(*** free variables ***)
let rec fv_msg m = match m with
    Name(x) -> [x]
  | Unit -> []
  | Pair(m1,m2) -> (fv_msg m1) @ (fv_msg m2)
  | Inl(m) -> fv_msg m
  | Inr(m) -> fv_msg m
  | EncSym(m,k) -> (fv_msg m) @ (fv_msg k)
  | EncAsym(m,k) -> (fv_msg m) @ (fv_msg k)

let set_sub s x = 
   List.filter (fun y -> not(x=y)) s

let union s1 s2 =Utilities.merge_and_unify compare s1 s2

let rec fv_proc p = match p with
    Zero -> []
  | Out(m,n) -> union (fv_msg m) (fv_msg n)
  | In(m,x,_,pr) -> union (fv_msg m) (set_sub (fv_proc pr) (ENname(x)))
  | OutS(m,n) -> union (fv_msg m) (fv_msg n)
  | InS(m,x,_,pr) -> union (fv_msg m) (set_sub (fv_proc pr) (ENname(x)))
  | Par(pr1,pr2) -> union (fv_proc pr1) (fv_proc pr2)
  | Nu(x,_,pr) -> (set_sub (fv_proc pr) (ENname(x)))
  | NuS(x,_,pr) -> (set_sub (fv_proc pr) (ENname(x)))
  | NuSym(x,_,pr) -> (set_sub (fv_proc pr) (ENname(x)))
  | NuAsym(x,_,y,_,pr) -> (set_sub (set_sub (fv_proc pr) (ENname(x))) (ENname(y)))
  | Check(x,y,pr) -> union [ENname(x)] (union [ENname(y)] (fv_proc pr))
  | DecSym(m,x,_,k,pr) -> union (fv_msg m) (union (fv_msg k) (set_sub (fv_proc pr) (ENname(x))))
  | DecAsym(m,x,_,k,pr) -> union (fv_msg m) (union (fv_msg k) (set_sub (fv_proc pr) (ENname(x))))
  | Case(m,y,_,pr1,z,_,pr2) -> 
           union (fv_msg m) (union (set_sub (fv_proc pr1) (ENname(y))) (set_sub (fv_proc pr2) (ENname(z))))
  | Split(m,y,_,z,_,pr) -> 
          union (fv_msg m) (set_sub (set_sub (fv_proc pr) (ENname(y))) (ENname(z)))
  | Match(m,y,z,_,pr) -> 
         union (fv_msg m) (union [ENname(y)] (set_sub (fv_proc pr) (ENname(z))))
  | Begin(m,pr) -> union (fv_msg m) (fv_proc pr)
  | End(m) -> fv_msg m
  | Copy(pr) -> (fv_proc pr)

exception Stype_failure of stype * stype
exception Unknown_variable of ex_name

let comp_subst subs s1 s2 = 
  let s2' = List.map (fun (ty1,ty2) -> (ty1,subs s1 ty2)) s2 in
  let s1' = List.filter (fun (ty1,ty2) -> List.for_all (fun (ty1',ty2') -> ty1!=ty1') s2) s1 in
    s1' @ s2'

let subst_var s t1 t2 = 
  try
    List.assoc t1 s
  with
    Not_found -> t2

let rec tsubst s t = match t with
    TUnit -> TUnit
  | TName(Pub) -> TName(Pub)
  | TName(Pr)  -> TName(Pr)
  | TPair(ty1,ty2) -> TPair(tsubst s ty1,tsubst s ty2)
  | TVari(ty1,ty2) -> TVari(tsubst s ty1,tsubst s ty2)
  | TChan(ty) -> TChan(tsubst s ty)
  | TSKey(ty) -> TSKey(tsubst s ty) 
  | TEKey(ty) -> TEKey(tsubst s ty) 
  | TDKey(ty) -> TDKey(tsubst s ty)
  | TVar(n) -> subst_var s (TVar(n)) t

let rec map_for_t f p = match p with
    Zero -> Zero
  | Out(m,n) -> Out(m,n)
  | In(m,x,ty,pr) -> In(m,x,f ty,map_for_t f pr)
  | OutS(m,n) -> OutS(m,n)
  | InS(m,x,ty,pr) -> InS(m,x,f ty,map_for_t f pr)
  | Par(pr1,pr2) -> Par(map_for_t f pr1,map_for_t f pr2)
  | Nu(x,ty,pr) -> Nu(x,f ty,map_for_t f pr)
  | NuS(x,ty,pr) -> NuS(x,f ty,map_for_t f pr)
  | NuSym(x,ty,pr) -> NuSym(x,f ty,map_for_t f pr)
  | NuAsym(x,tx,y,ty,pr) -> NuAsym(x,f tx,y,f ty,map_for_t f pr)
  | Check(x,y,pr) -> Check(x,y,map_for_t f pr)
  | DecSym(m,x,ty,k,pr) -> DecSym(m,x,f ty,k,map_for_t f pr)
  | DecAsym(m,x,ty,k,pr) -> DecAsym(m,x,f ty,k,map_for_t f pr)
  | Case(m,y,ty,pr1,z,tz,pr2) -> Case(m,y,f ty,map_for_t f pr1,z,f tz,map_for_t f pr2)
  | Split(m,y,ty,z,tz,pr) -> Split(m,y,f ty,z,f tz,map_for_t f pr)
  | Match(m,y,z,tz,pr) -> Match(m,y,z,f tz,map_for_t f pr)
  | Begin(m,pr) -> Begin(m,map_for_t f pr)
  | End(m) -> End(m)
  | Copy(pr) -> Copy(map_for_t f pr)


let tsubst_for_proc s = map_for_t (tsubst s)

let tinfVar x env =
  try
    env_lookup x env
  with
    Not_found -> raise (Unknown_variable(x))


let fresh_tyvar =
  let cnt = ref 0 in
  let body () =
    let v = !cnt in
      cnt := v + 1; v
  in body

let fresh_tv() = TVar(fresh_tyvar())

let env_extend2 x env =           (** stype variable for the free name  **)
     let xn = fresh_tyvar () in
      let ty_x = TVar(xn) in
         (x,ty_x)::env
  
(* [XXX] *)
let rec tinfV m env = match m with
    Name(x) -> (tinfVar x env,[]) 
  | Unit -> (TUnit,[])
  | Pair(m1,m2) -> 
      let (ty1,sc1) = tinfV m1 env in
      let (ty2,sc2) = tinfV m2 env in
	(TPair(ty1,ty2),sc1 @ sc2)
  | Inl(m') -> 
      let (ty,sc) = tinfV m' env in
	(TVari(ty, fresh_tv()),sc)
  | Inr(m') ->
      let (ty,sc) = tinfV m' env in
	(TVari(fresh_tv(),ty),sc)
  | EncSym(m',k) -> 
      let (ty_m,sc_m) = tinfV m' env in
      let (ty_k,sc_k) = tinfV k env in
	(TName(Pub),[(ty_k,TSKey(ty_m))] @ sc_m @ sc_k)
  | EncAsym(m',k) -> 
      let (ty_m,sc_m) = tinfV m' env in
      let (ty_k,sc_k) = tinfV k env in
	(TName(Pub),[(ty_k,TEKey(ty_m))] @ sc_m @ sc_k)
  (* | Int(n) -> TInt(fresh_predciate_variable, ...) *)


(*** Simple Type Infefence: unit procexp -> stype procexp * st_constraints ***)
let rec tinf p env = match p with
    Zero -> (Zero,[],[])
  | Out(m,n) -> 
      let (ty_m,sc_m) = tinfV m env in
      let (ty_n,sc_n) = tinfV n env in
	(Out(m,n),sc_m @ sc_n@[(ty_m,TName(Pub))],[(ty_m,Pub);(ty_n,Pub)])
  | OutS(m,n) -> 
      let (ty_m,sc_m) = tinfV m env in
      let (ty_n,sc_n) = tinfV n env in
	(OutS(m,n),sc_m @ sc_n @ [(ty_m,TChan(ty_n))],[])
  | In(m,x,_,pr) -> 
      let (ty_m,sc_m) = tinfV m env in
      let xn = fresh_tyvar () in
      let ty_x = TVar(xn) in
      let env' = env_extend (ENname(x)) ty_x env in
      let _ = (Pprint.print_env env') in
      let (pr',sc_p,pub_t) = tinf pr env' in
	(In(m,x,ty_x,pr'),sc_m @ sc_p @[(ty_m,TName(Pub))],(Utilities.merge_and_unify compare [(ty_x,Pub);(ty_m,Pub)] pub_t))
 | InS(m,x,_,pr) -> 
      let (ty_m,sc_m) = tinfV m env in
      let xn = fresh_tyvar () in
      let ty_x = TVar(xn) in
      let env' = env_extend (ENname(x)) ty_x env in
      let (pr',sc_p,pub_t) = tinf pr env' in
	(InS(m,x,ty_x,pr'),sc_m @ sc_p @ [(ty_m,TChan(ty_x))],pub_t)
  | Par(pr1,pr2) -> 
      let (pr1',sc1,pub_t1) = tinf pr1 env in
      let (pr2',sc2,pub_t2) = tinf pr2 env in
	(Par(pr1',pr2'),sc1 @ sc2,(Utilities.merge_and_unify compare pub_t1 pub_t2))
  | Nu(x,_,pr) -> 
      let xn = fresh_tyvar () in
      let ty_x = TVar(xn) in
      let _ = (Pprint.print_env env) in
      let env' = env_extend (ENname(x)) ty_x env in
      let (pr',sc_p,pub_t) = tinf pr env' in
	(Nu(x,ty_x,pr'),sc_p,pub_t)
  | NuS(x,_,pr) -> 
      let xn = fresh_tyvar () in
      let ty_x = TVar(xn) in
      let env' = env_extend (ENname(x)) (TChan(ty_x)) env in
      let (pr',sc_p,pub_t) = tinf pr env' in
	(NuS(x,TChan(ty_x),pr'),sc_p,pub_t)
  | NuSym(x,_,pr) -> 
      let xn = fresh_tyvar () in
      let ty_x = TVar(xn) in
      let env' = env_extend (ENname(x)) (TSKey(ty_x)) env in
      let _ = (Pprint.print_env env') in
      let (pr',sc_p,pub_t) = tinf pr env' in
	(NuSym(x,TSKey(ty_x),pr'),sc_p,pub_t)
  | NuAsym(x,_,y,_,pr) -> 
      let xn = fresh_tyvar () in
      let ty_x = TVar(xn) in
      let yn = fresh_tyvar () in
      let ty_y = TVar(yn) in
      let env' = env_extend (ENname(x)) (TEKey(ty_x)) env in
      let env''= env_extend (ENname(y)) (TDKey(ty_y)) env' in
      let (pr',sc_p,pub_t) = tinf pr env'' in
	(NuAsym(x,TEKey(ty_x),y,TDKey(ty_y),pr'),[(ty_x,ty_y);(ty_y,ty_x)]@sc_p,pub_t)
  | Check(x,y,pr) -> 
      let (ty_x,sc_n) = tinfV (Name(ENname(x))) env in
      let (ty_y,sc_n') = tinfV (Name(ENname(y))) env in
      let (pr',sc_p,pub_t) = tinf pr env in
      let _ = (Pprint.print_constraint_name "check" (sc_n@sc_n'@sc_p@[(ty_x,ty_y);(ty_y,ty_x)])) in
	(Check(x,y,pr'),sc_n@sc_n'@sc_p@[(ty_x,ty_y);(ty_y,ty_x)],pub_t)  
  | DecSym(m,x,_,k,pr) -> 
      let (ty_m,sc_m) = tinfV m env in
      let (ty_k,sc_k) = tinfV k env in
      let xn = fresh_tyvar () in
      let ty_x = TVar(xn) in
      let env' = env_extend (ENname(x)) ty_x env in
      let _ = (Pprint.print_env env') in
      let (pr',sc_p,pub_t) = tinf pr env' in
      let _ = (Pprint.print_constraint_name "dec" (sc_m @ sc_k @ sc_p @[(ty_m,TName(Pub));(ty_k,TSKey(ty_x))])) in
	(DecSym(m,x,ty_x,k,pr'),sc_m @ sc_k @ sc_p @[(ty_m,TName(Pub));(ty_k,TSKey(ty_x))],(Utilities.merge_and_unify compare [(ty_m,Pub)] pub_t))
  | DecAsym(m,x,_,k,pr) -> 
      let (ty_m,sc_m) = tinfV m env in
      let (ty_k,sc_k) = tinfV k env in
      let xn = fresh_tyvar () in
      let ty_x = TVar(xn) in
      let env' = env_extend (ENname(x)) ty_x env in
      let (pr',sc_p,pub_t) = tinf pr env' in
	(DecAsym(m,x,ty_x,k,pr'),sc_m @ sc_k @ sc_p @ [(ty_m,TName(Pub));(ty_k,TDKey(ty_x))],Utilities.merge_and_unify compare [(ty_m,Pub)] pub_t)
  | Case(m,y,_,pr1,z,_,pr2) -> 
      let (ty_m,sc_m) = tinfV m env in
      let yn = fresh_tyvar () in
      let ty_y = TVar(yn) in
      let env' = env_extend (ENname(y)) ty_y env in
      let (pr1',sc_p1,pub_t1) = tinf pr1 env' in
      let zn = fresh_tyvar () in
      let ty_z = TVar(zn) in
      let env'' = env_extend (ENname(z)) ty_z env in
      let (pr2',sc_p2,pub_t2) = tinf pr2 env'' in
	(Case(m,y,ty_y,pr1',z,ty_z,pr2'),sc_m @ sc_p1 @ sc_p2 @ [(ty_m,TVari(ty_y,ty_z))],(Utilities.merge_and_unify compare pub_t1 pub_t2))
  | Split(m,y,_,z,_,pr) -> 
      let (ty_m,sc_m) = tinfV m env in
      let yn = fresh_tyvar () in
      let ty_y = TVar(yn) in
      let zn = fresh_tyvar () in
      let ty_z = TVar(zn) in 
      let env' = env_extend (ENname(z)) ty_z (env_extend (ENname(y)) ty_y env) in
      let (pr',sc_p,pub_t) = tinf pr env' in
	(Split(m,y,ty_y,z,ty_z,pr'),sc_m @ sc_p @ [(ty_m,TPair(ty_y,ty_z))],pub_t)
  | Match(m,y,z,_,pr) -> 
      let (ty_m,sc_m) = tinfV m env in
      let ty_y = tinfVar (ENname(y)) env in
      let zn = fresh_tyvar () in
      let ty_z = TVar(zn) in 
      let env' = env_extend (ENname(z)) ty_z  env in
      let (pr',sc_p,pub_t) = tinf pr env' in
	(Match(m,y,z,ty_z,pr'),sc_m @ sc_p @ [(ty_m,TPair(ty_y,ty_z))],pub_t)
  | Begin(m,pr) -> 
      let (ty_m,sc_m) = tinfV m env in
      let (pr',sc_p,pub_t) = tinf pr env in
	(Begin(m,pr'),sc_m @ sc_p,pub_t)
  | End(m) -> 
      let (ty_m,sc_m) = tinfV m env in
      let _ = (Pprint.print_constraint_name "end" sc_m) in
	(End(m),sc_m,[])

  | Copy(pr) ->
      let (pr',sc_p,pub_t) = tinf pr env in
         (Copy(pr'),sc_p,pub_t)


  

(****************************    for (Pub|Pr)      ***********************)


let rec pub_for_c c pub_t =
      match c with
       [] -> []
      |(m,n)::res ->
         
          ( match (m,n) with
             (TVar(a),TVar(b)) ->
                    if (List.mem (TVar(a),Pub) pub_t) 
                    then  
                   Utilities.merge_and_unify compare  [(TVar(a),Pub);(TVar(b),Pub)] (pub_for_c res pub_t)         
                    else   (pub_for_c res pub_t)
	   
       	     |(_,_) -> (pub_for_c res pub_t)
          )
      




let rec pub_for_t ty =
    match ty with
       TVar(n) -> [(TVar(n),Pub)]
      |TPair(ta,tb)->(pub_for_t ta)@(pub_for_t tb)
      |TSKey(t)->(pub_for_t t)
      |TVari(t1,t2)->(pub_for_t t1)@(pub_for_t t2)
      |TDKey(t)->(pub_for_t t)
      |TChan(t)->(pub_for_t t)     
      |_ -> [] 

let rec make_pub_t t =
      match t with
        | TVar(a)  ->
                   [(TVar(a),Pub)]
        | TPair(x,y) ->
                    pub_for_t (TPair(x,y))
	| TSKey(t) ->        
                    pub_for_t (TSKey(t))                          
        | TDKey(t) ->               
                    pub_for_t (TDKey(t)) 
        | TChan(t) ->
                    pub_for_t (TChan(t))
	| TVari(t1,t2) ->
                    pub_for_t (TVari(t1,t2))
       	| _ -> []
  
let rec teq_for_k t1 t2 =    (***  to make relation of tvar in Tkey ***)
       match (t1,t2) with
    (TVar(a),TVar(b)) ->[(TVar(a),TVar(b))]@ [(TVar(b),TVar(a))]
  | (TSKey(t1),TSKey(t2)) -> teq_for_k t1 t2
  | (TChan(t1),TChan(t2)) -> teq_for_k t1 t2
  | (TEKey(t1),TDKey(t2)) -> teq_for_k t1 t2
  | (TEKey(t1),TEKey(t2)) -> teq_for_k t1 t2
  | (TDKey(t1),TDKey(t2)) -> teq_for_k t1 t2
  | (TPair(t1,t2),TPair(t1',t2')) -> Utilities.merge_and_unify compare (teq_for_k t1 t1')   (teq_for_k t2 t2')
  | (TVari(t1,t2),TVari(t1',t2')) -> Utilities.merge_and_unify compare (teq_for_k t1 t1')   (teq_for_k t2 t2')
  | (_,_) ->[]        

let rec tinf2 p' env  = match p' with
    Zero -> (Zero,[],[],[])
  | Out(m,n) -> 
      let (ty_m,sc_m) = tinfV m env in
      let (ty_n,sc_n) = tinfV n env in
	(Out(m,n),[],(make_pub_t ty_m)@(make_pub_t ty_n),env)

  | OutS(m,n) -> 
      let (ty_m,sc_m) = tinfV m env in
      let (ty_n,sc_n) = tinfV n env in
	(OutS(m,n),(teq_for_k ty_m (TChan(ty_n))),[],env)
  | In(m,x,ty_x,pr) -> 
      let env' = env_extend (ENname(x)) ty_x env in
      let (ty_m,sc_m) = tinfV m env in
      let (pr',teq_c,pub_c,env_p) = tinf2 pr env' in
    
	(In(m,x,ty_x,pr'),teq_c , (make_pub_t ty_m)@(make_pub_t ty_x)@pub_c,(Utilities.merge_and_unify compare env' env_p))
  | InS(m,x,ty_x,pr) -> 
      let env' = env_extend (ENname(x)) ty_x env in
      let (ty_m,sc_m) = tinfV m env in
      let (pr',teq_c,pub_c,env_p) = tinf2 pr env' in
	(InS(m,x,ty_x,pr'),(teq_for_k ty_m (TChan(ty_x)))@teq_c,pub_c,env)
  | Par(pr1,pr2) -> 
      let (pr1',teq_c1,pub_c1,env1) = tinf2 pr1 env in
      let (pr2',teq_c2,pub_c2,env2) = tinf2 pr2 env in
	(Par(pr1',pr2'), teq_c1@teq_c2, pub_c1@pub_c2,(Utilities.merge_and_unify compare env1 env2))
 | NuS(x,ty_x,pr) -> 
      let env' = env_extend (ENname(x)) ty_x env in
      let (pr',teq_c,pub_c,env_p) = tinf2 pr env' in
	(NuS(x,ty_x,pr'),teq_c,pub_c,env')

  | Nu(x,ty_x,pr) -> 
      let env' = env_extend (ENname(x)) ty_x env in
      let (pr',teq_c,pub_c,env_p) = tinf2 pr env' in
	(Nu(x,ty_x,pr'),teq_c,pub_c,(Utilities.merge_and_unify compare env' env_p))
  | NuSym(x,ty_x,pr) -> 
      let env' = env_extend (ENname(x)) ty_x env in
      let (pr',teq_c,pub_c,env_p) = tinf2 pr env' in
	(NuSym(x,ty_x,pr'),teq_c,pub_c,(Utilities.merge_and_unify compare env_p env'))
  | NuAsym(x,ty_x,y,ty_y,pr) -> 
      let env' = env_extend (ENname(x)) ty_x env in
      let env'' = env_extend (ENname(y)) ty_y env' in
      let (pr',teq_c,pub_c,env_p) = tinf2 pr env'' in
	(NuAsym(x,ty_x,y,ty_y,pr'), (teq_for_k ty_x ty_y)@teq_c,pub_c,(Utilities.merge_and_unify compare env'' env_p))
  | Check(x,y,pr) -> 
      let (ty_x,sc_n) = tinfV (Name(ENname(x))) env in
      let (ty_y,sc_n') = tinfV (Name(ENname(y))) env in
      let (pr',teq_c,pub_c,env_p) = tinf2 pr env in
	(Check(x,y,pr'), (teq_for_k ty_x ty_y)@teq_c,pub_c,(Utilities.merge_and_unify compare env env_p))  

  | DecSym(m,x,ty_x,k,pr) -> 
      let (ty_m,sc_m) = tinfV m env in
      let (ty_k,sc_k) = tinfV k env in
      let env' = env_extend (ENname(x)) ty_x env in
      let (pr',teq_c,pub_c,env_p) = tinf2 pr env' in
	(DecSym(m,x,ty_x,k,pr'), (teq_for_k (TSKey(ty_x)) ty_k)@teq_c,(make_pub_t ty_m)@pub_c,(Utilities.merge_and_unify compare env_p env'))


   | DecAsym(m,x,ty_x,k,pr) -> 
      let (ty_m,sc_m) = tinfV m env in
      let (ty_k,sc_k) = tinfV k env in
      let env' = env_extend (ENname(x)) ty_x env in
      let (pr',teq_c,pub_c,env_p) = tinf2 pr env' in
	(DecAsym(m,x,ty_x,k,pr'), (teq_for_k (TDKey(ty_x)) ty_k)@teq_c, (make_pub_t ty_m)@pub_c,(Utilities.merge_and_unify compare env_p env'))

    | Case(m,y,ty_y,pr1,z,ty_z,pr2) -> 
      let (ty_m,sc_m) = tinfV m env in
      let env' = env_extend (ENname(y)) ty_y env in
      let (pr1',teq_c1,pub_c1,env_p1) = tinf2 pr1 env' in
      let env'' = env_extend (ENname(z)) ty_z env in
      let (pr2',teq_c2,pub_c2,env_p2) = tinf2 pr2 env'' in
	(Case(m,y,ty_y,pr1',z,ty_z,pr2'),(teq_for_k ty_m (TVari(ty_y,ty_z)))@teq_c1@teq_c2,pub_c1@pub_c2,Utilities.merge_and_unify compare env_p1 env_p2)

  | Split(m,y,ty_y,z,ty_z,pr) -> 
      let (ty_m,sc_m) = tinfV m env in
      let env' = env_extend (ENname(z)) ty_z (env_extend (ENname(y)) ty_y env) in
      let (pr',teq_c,pub_c,env_p) = tinf2 pr env' in
	(Split(m,y,ty_y,z,ty_z,pr'),(teq_for_k ty_m (TPair(ty_y,ty_z)))@teq_c ,pub_c,(Utilities.merge_and_unify compare env_p env'))


  | Match(m,y,z,ty_z,pr) -> 
      let (ty_m,sc_m) = tinfV m env in
      let ty_y = tinfVar (ENname(y)) env in
      let env' = env_extend (ENname(z)) ty_z (env_extend (ENname(y)) ty_y env) in
      let (pr',teq_c,pub_c,env_p) = tinf2 pr env' in
	(Match(m,y,z,ty_z,pr'), (teq_for_k ty_m (TPair(ty_y,ty_z)))@teq_c,pub_c, Utilities.merge_and_unify compare env_p env')
  | Begin(m,pr) -> 
      let (ty_m,sc_m) = tinfV m env in
      let (pr',teq_c,pub_c,env_p) = tinf2 pr env in
	(Begin(m,pr'),teq_c,pub_c,env_p)
  | End(m) -> 
      let (ty_m,sc_m) = tinfV m env in
	(End(m),[],[],env)

  | Copy(pr) ->
      let (pr',teq_c,pub_c,env_p) = tinf2 pr env in
         (Copy(pr'),teq_c,pub_c,env_p)




 

let unif c =
  let subst_for_c s c =
    List.map (fun (ty1,ty2) -> (tsubst s ty1,tsubst s ty2)) c
  in
  let rec unif_aux (c,s) = match c with
      [] -> s
    | (ty1,ty2)::tl -> if ty1=ty2 then unif_aux (tl,s) else match (ty1,ty2) with
	  (TVar(n),_) -> 
	    let s1 = [(TVar(n),ty2)] in
	    let s2 = comp_subst tsubst s1 s in
	    let t1' = subst_for_c s1 tl in 
	      unif_aux (t1',s2)
	| (_,TVar(n)) -> unif_aux ((ty2,ty1)::tl,s)
	| (TPair(ty1,ty2),TPair(ty1',ty2')) -> unif_aux ((ty1,ty1')::((ty2,ty2')::tl),s)
	| (TVari(ty1,ty2),TVari(ty1',ty2')) -> unif_aux ((ty1,ty1')::((ty2,ty2')::tl),s)
	| (TSKey(ty),TSKey(ty')) -> unif_aux ((ty,ty')::tl,s)
	| (TEKey(ty),TEKey(ty')) -> unif_aux ((ty,ty')::tl,s)
	| (TDKey(ty),TDKey(ty')) -> unif_aux ((ty,ty')::tl,s)
	| (TChan(ty),TChan(ty')) -> unif_aux ((ty,ty')::tl,s)
        | _ -> raise (Stype_failure(ty1,ty2)) 
  in
    unif_aux (c,[])

let rec specify_type_for_pub pub_t t =
  match t with
    TUnit -> TUnit
  | TName(Pub) -> TName(Pub)
  | TName(Pr) -> TName(Pr)
  | TPair(ty1,ty2) -> TPair(specify_type_for_pub pub_t ty1,specify_type_for_pub pub_t ty2)
  | TVari(ty1,ty2) -> TVari(specify_type_for_pub pub_t ty1,specify_type_for_pub pub_t ty2)
  | TSKey(ty) -> TSKey(specify_type_for_pub pub_t ty)
  | TEKey(ty) -> TEKey(specify_type_for_pub pub_t ty)
  | TDKey(ty) -> TDKey(specify_type_for_pub pub_t ty)
  | TChan(ty) -> TChan(specify_type_for_pub pub_t ty)
  | TVar(n) -> if (List.mem (TVar(n),Pub) pub_t)
                 then TName(Pub)  
                 else TVar(n)

let rec specify_type t = match t with
    TUnit -> TUnit
  | TName(Pub) -> TName(Pub)
  | TName(Pr) -> TName(Pr)
  | TPair(ty1,ty2) -> TPair(specify_type ty1,specify_type ty2)
  | TVari(ty1,ty2) -> TVari(specify_type ty1,specify_type ty2)
  | TSKey(ty) -> TSKey(specify_type ty)
  | TEKey(ty) -> TEKey(specify_type ty)
  | TDKey(ty) -> TDKey(specify_type ty)
  | TChan(ty) -> TChan(specify_type ty)
  | TVar(n) -> TName(Pr)

let rec unif_env2 (a,b) l =
   match l with 
       []->[]
     | (x,y)::res ->
         if a=x then [(b,y)]@(unif_env2 (a,b) res)
         else (unif_env2 (a,b) res)

let rec unif_env env = 
  match env with
   [] -> []
  |(a,b)::res ->
       (unif_env2 (a,b) res)@unif_env res

let rec env_stype env pubt =
   match env with 
      [] -> []
     |(a,b)::res -> if (List.mem (b,Pub) pubt) 
       then [(a,TName(Pub))]@(env_stype res pubt)
       else [(a,TName(Pr))]@(env_stype res pubt) 


(***  test   ***)

(***
let rec pub_for_t ty =
    match ty with
       TVar(n) -> [(TVar(n),Pub)]
      |TPair(ta,tb)->(pub_for_t ta)@(pub_for_t tb)
      |TSKey(t)->(pub_for_t t)
      |TDKey(t)->(pub_for_t t)     
      |_ -> [] 
***)

let rec pub_for_c2 f l pub_c =
     match l with
	 [] -> []
       | (TVar(a),ty)::res ->
	   if (List.mem (TVar(a),Pub) pub_c) then
             Utilities.merge_and_unify compare (f ty) (pub_for_c2 f res pub_c)
           else 
             (pub_for_c2 f res pub_c)
       | (_,_)::res -> pub_for_c2 f res pub_c

(*** stype_inf: unit procexp -> stype procexp * stype env ***)
let rec stype_inf (p: unit procexp) = 
  let fv = fv_proc p in
  let env = List.fold_left (fun env -> fun x -> env_extend2 x  env) [] fv in
  let (p',c,pub_t) = tinf p env in
  let _ = (Pprint.print_constraint c) in
  let _ = (Pprint.ppp_proc p') in  
  let s = unif c in
  let _ = (Pprint.print_constraint_name "uni" s) in
  let p'' = tsubst_for_proc s p' in 
  let (p'',teq_c,pub_c,env_c) = tinf2 p'' env in
  let _ = (Pprint.ppp_proc p'') in
  let pub_c' =  (pub_for_c teq_c pub_c)@pub_t    in
  let _ = (Pprint.print_constraint_name "teq_c" teq_c) in
  let p''' = map_for_t (specify_type_for_pub pub_c') p'' in
  let p'''' = map_for_t specify_type p''' in
  let env'' = env_stype env pub_c' in
    (p'''',env'')



    




    



    