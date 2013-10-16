
(* Bool.andb *)
let andb = Pervasives.(&&)
  
(* Bool.orb *)
let orb = Pervasives.(||)
  
(* Bool.^^ *)
let cfcf (x:bool) (y:bool) : bool = 
  Obj.magic ((Obj.magic x) lxor (Obj.magic y))
  
(* Bool.notb *)
let notb = Pervasives.not
  
(* Bool.implb *)
let implb = EcPervasive.eqgt
  
(* Bool.Dbool *)
module Dbool = struct
  
  (* Bool.Dbool.dbool *)
  let dbool : EcPervasive.bool0 EcPervasive.distr =
     fun _ -> Random.bool ()

end
