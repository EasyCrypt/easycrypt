(** Defines higher level tactics using low level functions from Ec.Api. 
* From the toplevel, they can be used after having loaded them by:
#use "src/usrTac.ml";; 
**)

open Ec.Api

let trivial () =
  wp_asgn ();
  tac_prove ()

