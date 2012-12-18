(* Finite map : dynamic |-> t *)

open Deriving_Typeable
open Deriving_Eq

module Comp (T : Typeable) (E : Eq with type a = T.a) :
sig
  type a = T.a
  val eq : dynamic -> dynamic -> bool
end

module DynMap :
sig
  type comparator = dynamic -> dynamic -> bool
  type 'a t
   val empty : 'a t
   val add : dynamic -> 'a -> comparator -> 'a t -> 'a t 
   val mem : dynamic -> 'a t -> bool 
   val find : dynamic -> 'a t -> 'a option
   val iter : (dynamic -> 'a -> unit) -> 'a t -> unit
end
