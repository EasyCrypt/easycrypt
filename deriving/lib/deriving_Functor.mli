module type Functor = 
sig
  type 'a f
  val map : ('a -> 'b) -> 'a f -> 'b f 
end
module MonadFunctor (M : Deriving_monad.Monad) : Functor with type 'a f = 'a M.m
module Functor_option : Functor with type 'a f = 'a option
module Functor_list : Functor with type 'a f = 'a list
module Functor_map (O : Map.OrderedType) : Functor with type 'a f = 'a Map.Make(O).t
