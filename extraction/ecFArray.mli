(* Array.array *)
type 'x array

(*val array: 'x array -> 'x array *)
  
(* Array.length *)
val length : 'x array -> EcPervasive.int0 
  
(* Array.`|_| *)
val bqbr_br : 'x array -> EcPervasive.int0 
  
(* Array._.[_] *)
val _dtlb_rb : 'x array -> EcPervasive.int0 -> 'x 
  
(* Array.empty *)
val empty : 'x array 
  
(* Array._::_ *)
val _clcl_ : 'x -> 'x array -> 'x array
  
(* Array.::: *)
val clclcl : 'x array -> 'x -> 'x array 
  
(* Array._.[_<-_] *)
val _dtlb_lsmn_rb : 'x array -> EcPervasive.int0 -> 'x -> 'x array 
  
(* Array.make *)
val make : EcPervasive.int0 -> 'x -> 'x array 
  
(* Array.init *)
val init : EcPervasive.int0 -> (EcPervasive.int0 -> 'x) -> 'x array 
  
(* Array.|| *)
val brbr : 'x array -> 'x array -> 'x array 
  
(* Array.sub *)
val sub : 'x array -> EcPervasive.int0 -> EcPervasive.int0 -> 'x array 
  
(* Array.fill *)
val fill : 'x array ->
               EcPervasive.int0 -> EcPervasive.int0 -> 'x -> 'x array 
  
(* Array.blit *)
val blit : 'x array ->
               EcPervasive.int0 ->
                 'x array -> EcPervasive.int0 -> EcPervasive.int0 -> 'x array 
  
(* Array.map *)
val map : ('x -> 'y) -> 'x array -> 'y array 
  
(* Array.map2 *)
val map2 : ('x -> 'y -> 'z) -> 'x array -> 'y array -> 'z array 
  
(* Array.mapi *)
val mapi : (EcPervasive.int0 -> 'x -> 'y) -> 'x array -> 'y array 
  
(* Array.fold_left *)
val fold_left : ('state -> 'x -> 'state) -> 'state -> 'x array -> 'state 
  
(* Array.fold_right *)
val fold_right : ('state -> 'x -> 'state) -> 'state -> 'x array -> 'state 
  
(* Array.all *)
val all : ('x -> EcPervasive.bool0) -> 'x array -> EcPervasive.bool0 
  
(* Array.alli *)
val alli : (EcPervasive.int0 -> 'x -> EcPervasive.bool0) ->
               'x array -> EcPervasive.bool0 
  
(* Array.Darray *)
module Darray : sig
  
  (* Array.Darray.darray *)
  val darray : EcPervasive.int0 ->
                   'a EcPervasive.distr -> 'a array EcPervasive.distr 

end
