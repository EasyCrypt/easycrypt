(* Array.array *)
type 'x tarray = 'x array

type 'x array = 'x tarray
  
(* Array.init *)
let init = Array.init
  
(* Array.create *)
let create = Array.make 

(* Array.empty *)
(* TODO : how to implement this ? *)
(*
let empty : 'a array = ( (Obj.magic (Array.make 0 ())) : 'a array)
*)
  
(* Array._.[_] *)
let _dtlb_rb = Array.get 

(* Array._.[_<-_] *)
let _dtlb_lsmn_rb = Array.set 
  
(* Array.length *)
let length = Array.length
  
(* Array.write *)
let write dst dOff src sOff len = Array.blit src sOff dst dOff len
  
(* Array.map2 *)
let map2 f t1 t2 = 
  let len = min (Array.length t1) (Array.length t2) in
  Array.init len (fun i -> f t1.(i) t2.(i))

(* Array.map *)
let map = Array.map
  
(* Array.fold_left *)
let fold_left f t s = 
  Array.fold_left (fun s x -> f x s) s t
  
(* Array.fold_right *)
let fold_right f s t = 
  Array.fold_right (fun x s -> f s x) t s
  
(* Array.sub *)
let sub = Array.sub 
  
(* Array.|| *)
let brbr = Array.append 
  
(* Array.::: *)
let clclcl t x = 
  let len = Array.length t in
  let res = Array.make (len + 1) x in
  Array.blit t 0 res 0 len
  
(* Array._::_ *)
let _clcl_ x t = 
  let len = Array.length t in
  let res = Array.make (len + 1) x in
  Array.blit t 0 res 1 len 
  




