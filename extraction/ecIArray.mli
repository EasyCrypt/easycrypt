(* Array.array *)
type 'x tarray

val array: 'x array -> 'x tarray
  
(* Array.length *)
val length : 'x tarray -> EcPervasive.int0 
  
(* Array.`|_| *)
val bqbr_br : 'x tarray -> EcPervasive.int0 
  
(* Array._.[_] *)
val _dtlb_rb : 'x tarray -> EcPervasive.int0 -> 'x 
  
(* Array.empty *)
val empty : 'x tarray 
  
(* Array._::_ *)
val _clcl_ : 'x -> 'x tarray -> 'x tarray
  
(* Array.::: *)
val clclcl : 'x tarray -> 'x -> 'x tarray 
  
(* Array._.[_<-_] *)
val _dtlb_lsmn_rb : 'x tarray -> EcPervasive.int0 -> 'x -> 'x tarray 
  
(* Array.make *)
val make : EcPervasive.int0 -> 'x -> 'x tarray 
  
(* Array.init *)
val init : EcPervasive.int0 -> (EcPervasive.int0 -> 'x) -> 'x tarray 
  
(* Array.|| *)
val brbr : 'x tarray -> 'x tarray -> 'x tarray 
  
(* Array.sub *)
val sub : 'x tarray -> EcPervasive.int0 -> EcPervasive.int0 -> 'x tarray 
  
(* Array.fill *)
val fill : 'x tarray ->
               EcPervasive.int0 -> EcPervasive.int0 -> 'x -> 'x tarray 
  
(* Array.blit *)
val blit : 'x tarray ->
               EcPervasive.int0 ->
                 'x tarray -> EcPervasive.int0 -> EcPervasive.int0 -> 'x tarray 
  
(* Array.map *)
val map : ('x -> 'y) -> 'x tarray -> 'y tarray 
  
(* Array.map2 *)
val map2 : ('x -> 'y -> 'z) -> 'x tarray -> 'y tarray -> 'z tarray 
  
(* Array.mapi *)
val mapi : (EcPervasive.int0 -> 'x -> 'y) -> 'x tarray -> 'y tarray 
  
(* Array.fold_left *)
val fold_left : ('state -> 'x -> 'state) -> 'state -> 'x tarray -> 'state 
  
(* Array.fold_right *)
val fold_right : ('state -> 'x -> 'state) -> 'state -> 'x tarray -> 'state 
  
(* Array.all *)
val all : ('x -> EcPervasive.bool0) -> 'x tarray -> EcPervasive.bool0 
  
(* Array.alli *)
val alli : (EcPervasive.int0 -> 'x -> EcPervasive.bool0) ->
               'x tarray -> EcPervasive.bool0 
  
(* Array.Darray *)
module Darray : sig
  
  (* Array.Darray.darray *)
  val darray : EcPervasive.int0 ->
                   'a EcPervasive.distr -> 'a tarray EcPervasive.distr 

end
