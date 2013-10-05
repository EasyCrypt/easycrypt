(* Bool.Dbool *)
module Dbool = struct

  (* Bool.Dbool.dbool *)
  let dbool :  EcPervasive.bool EcPervasive.distr = 
     fun _ -> Random.bool ()
  
end
  
(* Bool.implb *)
let implb = EcPervasive.eqgt 
  
(* Bool.notb *)
let notb = Pervasives.not
  
(* Bool.^^ *)
let cfcf (x:bool) (y:bool) : bool = 
  Obj.magic ((Obj.magic x) lxor (Obj.magic y))
  
(* Bool.orb *)
let orb = Pervasives.(||)
  
(* Bool.andb *)
let andb = Pervasives.(&&)


