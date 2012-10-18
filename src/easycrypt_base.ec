(* Extra operators on int *)
op [>] (x,y:int) = y < x as gt_int.
op [>=] (x,y:int) = y <= x as ge_int.

(* Extra operators on real *)
op [>] (x,y:real) = y < x as gt_real.
op [>=] (x,y:real) = y <= x as ge_real.

(* fst and snd *)

op fst (p : 'a * 'b) = 
  let a,b = p in a. 

op snd (p : 'a * 'b) = 
  let a,b = p in b.


(* option *)

axiom Some_inj : 
 forall (x, y : 'a),
  Some(x) = Some(y) => x = y.

op proj : 'a option -> 'a.

axiom Proj_Some : 
 forall (x: 'a),
  proj(Some(x)) = x.

axiom Proj_eq :
  forall (o1, o2: 'a option),
    !(o1 = None) => !(o2 = None) =>
    proj(o1) = proj(o2) =>
    o1 = o2.

axiom Some_or_None :
 forall (o: 'a option),
  o = None || exists (x: 'a), o = Some(x).

(* List *)

op hd : 'a list -> 'a.
op tl : 'a list -> 'a list. 

axiom head_def : 
  forall (a: 'a, l: 'a list),
    hd(a::l) = a.
