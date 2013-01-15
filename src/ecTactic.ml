
type intro_arg = 
  | IA_or of bool
  | IA_and of intro_args * intros_args
  | IA_id  of string
  | IA_exists of pformula
and intro_args = intro_arg list

module Logic = struct

  let t_trivial = EcEnv.Logic.t_trivial

  let t_intro 

type ptactic = 
  | Tidtac
  | Tassumption
  | Ttrivial
  | Trewrite
  | Tcase (* or_elim, and_elim, exists_elim *)
  | Tapply 
  | Tleft
  | Tright
  | Tand 
