
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
  let dbool : bool EcPervasive.distr =
     fun _ -> Random.bool ()

end
