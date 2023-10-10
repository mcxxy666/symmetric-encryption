
type ovarid = int

type poly = P of (ovarid * float) list * float
type ineq =
    Le of poly * float
  | Lt of poly * float

let normalize_ineq c =
  match c with
    Le(P(l, x), y) -> Le(P(l, 0.0), y-.x)
  | Lt(P(l, x), y) -> Lt(P(l, 0.0), y-.x)

let compare_unitterm (ov1, _) (ov2, _) = compare ov1 ov2

let zero_poly = P([], 0.0)

(*** let int_poly n = P([], float_of_int(n)) ***)
let int_poly n = P([], n) 

let var_poly v = P([(v, 1.0)], 0.0)

let scalar_poly f (P(ps, c)) =
  P(List.map (fun (ov, f') -> ov, (f *. f')) ps, c *. f)

let rec add_poly (P(ps1, c1)) (P(ps2, c2)) =
  let ps1, ps2 = List.sort compare_unitterm ps1, 
                List.sort compare_unitterm ps2 in
  let rec helper ps1 ps2 =
    match ps1, ps2 with
      | [], p | p, [] -> p
      | (x1, f1)::tl1, (x2, f2)::tl2 ->
	  let cmp = compare x1 x2 in
	    if cmp = 0 then (x1, f1 +. f2)::(helper tl1 tl2)
	    else if cmp < 0 then (x1, f1)::(helper tl1 ps2)
	    else (x2, f2)::(helper ps1 tl2)
  in
    P(helper ps1 ps2, c1 +. c2)

let neg_poly p = 
  scalar_poly (-1.0) p

let sub_poly p1 p2 =
  add_poly p1 (neg_poly p2)


