open Deriving_monad

(* Copyright Jeremy Yallop 2007.
   This file is free software, distributed under the MIT license.
   See the file COPYING for details.
*)

module type Functor = 
sig
  type 'a f
  val map : ('a -> 'b) -> 'a f -> 'b f
end

module MonadFunctor (M : Monad) 
  : Functor with type 'a f = 'a M.m
=
struct
  open M
  type 'a f = 'a M.m
  let map  f x = x >>= (fun x -> return (f x))
end


module Functor_option = MonadFunctor(Monad_option)
module Functor_list = MonadFunctor(Monad_list)

module Functor_map (O : Map.OrderedType) 
  : Functor with type 'a f = 'a Map.Make(O).t =
struct 
  include Map.Make(O)
  type 'a f = 'a t
end

(*
NB: Instances for mutable types (including

   ref
   queue
   stack
   array
   stream
   buffer)

are deliberately omitted.  Since sharing is detectable for values of
these types we have two distinct design choices:

  1. Always create a new copy that shares no structure with the
     original.

  2. Always mutate the original copy

Neither of these seems like the right thing to do, so instead we
simply don't handle mustable types at all.

(Lazy.t is another example: we'd like map to be total and side-effect
free, which is impossible to guarantee if we handle lazy.
*)
