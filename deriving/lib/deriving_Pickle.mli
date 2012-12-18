open Deriving_Typeable
open Deriving_Eq
open Deriving_Dump

type id

(* representation of values of user-defined types *)
module Repr : sig
  type t
  val make : ?constructor:int -> id list -> t
end 

(* Utilities for serialization *)
module Write : sig
  type s
  include Deriving_monad.Monad_state_type with type state = s
  module Utils (T : Typeable) (E : Eq with type a = T.a) : sig
    val allocate : T.a -> (id -> unit m) -> id m
    val store_repr : id -> Repr.t -> unit m
  end
end

(* Utilities for deserialization *)
module Read : sig
  type s
  include Deriving_monad.Monad_state_type with type state = s
  module Utils (T : Typeable) : sig
    val sum    : (int * id list -> T.a m)  -> (id -> T.a m)
    val tuple  : (id list -> T.a m)        -> (id -> T.a m)
    val record : (T.a -> id list -> T.a m) -> int -> (id -> T.a m)
  end
end

exception UnpicklingError of string
exception UnknownTag of int * string

module type Pickle =
sig
  type a
  module Typeable : Typeable with type a = a
  module Eq : Eq with type a = a
  val pickle : a -> id Write.m
  val unpickle : id -> a Read.m
  val to_buffer : Buffer.t -> a -> unit
  val to_string : a -> string
  val to_channel : out_channel -> a -> unit
  val from_stream : char Stream.t -> a
  val from_string : string -> a
  val from_channel : in_channel -> a
end

module Defaults
  (S : sig
     type a
     module Typeable : Typeable with type a = a
     module Eq : Eq with type a = a
     val pickle : a -> id Write.m
     val unpickle : id -> a Read.m
   end) : Pickle with type a = S.a

module Pickle_unit  : Pickle with type a = unit
module Pickle_bool  : Pickle with type a = bool
module Pickle_int   : Pickle with type a = int
module Pickle_char  : Pickle with type a = char
module Pickle_float : Pickle with type a = float
module Pickle_string : Pickle with type a = string
module Pickle_int32 : Pickle with type a = int32
module Pickle_int64 : Pickle with type a = int64
module Pickle_nativeint : Pickle with type a = nativeint
module Pickle_option (V0 : Pickle) : Pickle with type a = V0.a option
module Pickle_list (V0 : Pickle)  : Pickle with type a = V0.a list
module Pickle_ref (S : Pickle) : Pickle with type a = S.a ref

module Pickle_from_dump
  (P : Dump)
  (E : Eq with type a = P.a)
  (T : Typeable with type a = P.a)
  : Pickle with type a = P.a
