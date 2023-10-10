
type id = string

type name = string
type index = int
type ex_name = ENname of name
	     | ENindex of index

type message = Name of ex_name
	     | Unit 
	     | Pair of message * message 
             | Inl of message 
	     | Inr of message 
	     | EncSym of message * message
             | EncAsym of message * message
             

(*** process expresions ***)
type 'a procexp = Zero
		| Out of message * message
                | OutS of message * message
		| In of message * name * 'a * 'a procexp
            	| InS of message * name * 'a * 'a procexp
		| Par of 'a procexp * 'a procexp
		| Nu of name * 'a * 'a procexp
        	| NuS of name * 'a * 'a procexp 
                | NuSym of name * 'a * 'a procexp 
                | NuAsym of name * 'a * name * 'a * 'a procexp 
		| Check of name * name * 'a procexp
               	| Case of message * name * 'a * 'a procexp * name * 'a * 'a procexp	
		| DecSym of message * name * 'a * message * 'a procexp
  	        | DecAsym of message * name * 'a * message * 'a procexp
		| Split of message * name * 'a * name * 'a * 'a procexp
		| Match of message * name * name * 'a * 'a procexp
		| Begin of message * 'a procexp
		| End of message 
                | Copy of 'a procexp
               
(* { _nu : int | phi (....) }*)


(*** simple types ***)
type tid = int

type pp = Pub | Pr

type stype = TUnit			(*** () ***)
	   | TName of pp	        (*** N_l(e1,e2) ***)
	   | TPair of stype * stype 	(*** T1*T2 ***)
	   | TVari of stype * stype	(*** T1+T2 ***)
	   | TSKey of stype		(*** S_Key(T) ***)
	   | TChan of stype		(*** Key(T) ***)
           | TEKey of stype		(*** E_Key(T) ***)
           | TDKey of stype		(*** D_Key(T) ***)
	   | TVar of tid 		(*** type variables ***)
        

(*** types with effects ***)
type eid = int
type etype = ETUnit 
	   | ETName of pp * effect 
	   | ETPair of etype * etype 
	   | ETVari of etype * etype  
	   | ETSKey of etype
	   | ETChan of etype
           | ETEKey of etype
           | ETDKey of etype
           | ETany


 and effect = Emap of (atomic_effect * float) list 	(*** frac. effect ***)
	    | Evar of eid				(*** effect variables ***)
	    | Eplus of effect * effect 		(*** e1+e2 ***)
	    | Esub of index * name * effect 		(*** [m/i]e ***)
 and atomic_effect = AEend of message 	(*** end <m> ***)
		   | AEchk of pp * ex_name * effect	(*** chk_l<x,e> ***)

type atomic_constraint = ECeq of effect * effect 	(*** e1=e2 ***) 
		       | ECsub of effect * effect 	(*** e1>=e2 ***)
		       | ECnotin of ex_name * effect 	(*** notin(x,e) ***)
		       | ECfn of effect * ex_name list (*** fn(e) \subseteq N ***)
type ef_constraint = atomic_constraint list

let rec map_proc (f:'a -> 'b) (p: 'a procexp): 'b procexp = match p with
    Zero -> Zero
  | Out(m1,m2) -> Out(m1,m2) 
  | In(m,x, a, p') -> In(m, x, f a, map_proc f p')
  | OutS(m1,m2) -> OutS(m1,m2) 
  | InS(m,x, a, p') -> InS(m, x, f a, map_proc f p')
  | Par(p1,p2) -> Par(map_proc f p1, map_proc f p2)
  | Nu(x, a, p1) -> Nu(x, f a, map_proc f p1)
  | NuS(x, a, p1) -> NuS(x, f a, map_proc f p1)
  | NuSym(x, a, p1) -> NuSym(x, f a, map_proc f p1)
  | NuAsym(x1,a1,x2,a2,p1) -> NuAsym(x1, f a1, x2 , f a2 , map_proc f p1)
  | Check(x, m, p1) -> Check(x, m, map_proc f p1)
  | DecSym(m1,x,a,m2, p1) -> DecSym(m1,x, f a, m2, map_proc f p1)
  | DecAsym(m1,x,a,m2, p1) -> DecAsym(m1,x, f a, m2, map_proc f p1)
  | Case(m,x1,a1,p1,x2,a2,p2) -> Case(m,x1, f a1, map_proc f p1, x2, f a2, map_proc f p2)
  | Split(m,x1,a1,x2,a2,p1) -> Split(m,x1, f a1, x2, f a2, map_proc f p1)
  | Match(m,x1,x2,a2,p1) -> Match(m,x1, x2, f a2, map_proc f p1)
  | Begin(m, p1) -> Begin(m, map_proc f p1)
  | End(m) -> End(m)
  | Copy(p1) -> Copy(map_proc f p1)
    
let rec map_etype (f: effect -> effect) t = match t with
    ETUnit -> ETUnit
  | ETName(l,e1) -> ETName(l,f e1)
  | ETPair(t1,t2) -> ETPair(map_etype f t1, map_etype f t2)
  | ETVari(t1,t2) -> ETVari(map_etype f t1, map_etype f t2)
  | ETSKey(t1) -> ETSKey(map_etype f t1)
  | ETChan(t1) -> ETChan(map_etype f t1)
  | ETEKey(t1) -> ETEKey(map_etype f t1)
  | ETDKey(t1) -> ETDKey(map_etype f t1)
  | ETany -> ETany


