(* Array.array *)
type 'x array0

val array: 'x array -> 'x array0 
  
(* Array.length *)
val length : 'x array0 -> int 
  
(* Array.`|_| *)
val bqbr_br : 'x array0 -> int 
  
(* Array._.[_] *)
val _dtlb_rb : 'x array0 -> int -> 'x 
  
(* Array.empty *)
val empty : 'x array0 
  
(* Array._::_ *)
val _clcl_ : 'x -> 'x array0 -> 'x array0
  
(* Array.::: *)
val clclcl : 'x array0 -> 'x -> 'x array0 
  
(* Array._.[_<-_] *)
val _dtlb_lsmn_rb : 'x array0 -> int -> 'x -> 'x array0 
  
(* Array.make *)
val make : int -> 'x -> 'x array0 
  
(* Array.init *)
val init : int -> (int -> 'x) -> 'x array0 
  
(* Array.|| *)
val brbr : 'x array0 -> 'x array0 -> 'x array0 
  
(* Array.sub *)
val sub : 'x array0 -> int -> int -> 'x array0 
  
(* Array.fill *)
val fill : 'x array0 -> int -> int -> 'x -> 'x array0 
  
(* Array.blit *)
val blit : 'x array0 -> int -> 'x array0 -> int -> int -> 'x array0 
  
(* Array.map *)
val map : ('x -> 'y) -> 'x array0 -> 'y array0 
  
(* Array.map2 *)
val map2 : ('x -> 'y -> 'z) -> 'x array0 -> 'y array0 -> 'z array0 
  
(* Array.mapi *)
val mapi : (int -> 'x -> 'y) -> 'x array0 -> 'y array0 
  
(* Array.fold_left *)
val fold_left : ('state -> 'x -> 'state) -> 'state -> 'x array0 -> 'state 
  
(* Array.fold_right *)
val fold_right : ('state -> 'x -> 'state) -> 'state -> 'x array0 -> 'state 
  
(* Array.all *)
val all : ('x -> bool) -> 'x array0 -> bool 
  
(* Array.alli *)
val alli : (int -> 'x -> bool) ->
               'x array0 -> bool 
  
(* Array.Darray *)
module Darray : sig
  
  (* Array.Darray.darray *)
  val darray : int -> 'a EcPervasive.distr -> 'a array0 EcPervasive.distr 

end
