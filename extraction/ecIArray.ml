(* Array.array *)
type 'x tarray = 'x array

let array x = x
  
(* Array.length *)
let length = Array.length 
  
(* Array.`|_| *)
let bqbr_br (xs : 'x array) = length xs
  
(* Array._.[_] *)
let _dtlb_rb = Array.get
  
(* Array.empty *)
let empty : 'x array = [||]
  
(* Array._::_ *)
let _clcl_ x t = 
  let len = Array.length t in
  let res = Array.make (len + 1) x in
  Array.blit t 0 res 1 len;
  res

(* Array.::: *)
let clclcl t x = 
  let len = Array.length t in
  let res = Array.make (len + 1) x in
  Array.blit t 0 res 0 len;
  res

(* Array._.[_<-_] *)
let _dtlb_lsmn_rb : 'x array -> EcPervasive.int0 -> 'x -> 'x array =
  fun t i x ->
  Array.set t i x; t
  
(* Array.make *)
let make : EcPervasive.int0 -> 'x -> 'x array = 
  Array.make 
  
(* Array.init *)
let init : EcPervasive.int0 -> (EcPervasive.int0 -> 'x) -> 'x array =
  Array.init
  
(* Array.|| *)
let brbr : 'x array -> 'x array -> 'x array =
  Array.append
  
(* Array.sub *)
let sub : 'x array -> EcPervasive.int0 -> EcPervasive.int0 -> 'x array =
  Array.sub
  
(* Array.fill *)
let fill : 'x array ->
       EcPervasive.int0 -> EcPervasive.int0 -> 'x -> 'x array =
  fun t d o x -> 
    Array.fill t d o x;
    t
  
(* Array.blit *)
let blit dst dOff src sOff len = Array.blit src sOff dst dOff len; dst
  
(* Array.map *)
let map : ('x -> 'y) -> 'x array -> 'y array =
  Array.map
  
(* Array.map2 *)
let map2 f t1 t2 = 
  let len = min (Array.length t1) (Array.length t2) in
  Array.init len (fun i -> f t1.(i) t2.(i))

(* Array.mapi *)
let mapi : (EcPervasive.int0 -> 'x -> 'y) -> 'x array -> 'y array =
  Array.mapi
  
(* Array.fold_left *)
let fold_left : ('state -> 'x -> 'state) -> 'state -> 'x array -> 'state =
  Array.fold_left
  
(* Array.fold_right *)
let fold_right f s t =
  Array.fold_right (fun x s -> f s x) t s
  
(* Array.all *)
let all f t = 
  let rec aux i = i >= Array.length t || (not (f t.(i)) && aux (i+1)) in
  aux 0 
  
(* Array.alli *)
let alli f t = 
  let rec aux i = i >= Array.length t || (not (f i t.(i)) && aux (i+1)) in
  aux 0 
  
(* Array.Darray *)
module Darray = struct
  
  (* Array.Darray.darray *)
  let darray : EcPervasive.int0 ->
                'a EcPervasive.distr -> 'a array EcPervasive.distr =
     fun len d () -> Array.init len (fun _ -> d ()) 

end
