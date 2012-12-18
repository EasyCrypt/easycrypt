module type Dump =
  sig
    type a
    val to_buffer : Buffer.t -> a -> unit
    val to_string : a -> string
    val to_channel : out_channel -> a -> unit
    val from_stream : char Stream.t -> a
    val from_string : string -> a
    val from_channel : in_channel -> a
  end

module Defaults
  (P : sig
     type a
     val to_buffer : Buffer.t -> a -> unit
     val from_stream : char Stream.t -> a
   end) : Dump with type a = P.a

exception Dump_error of string

module Dump_int32     : Dump with type a = Int32.t
module Dump_int64     : Dump with type a = Int64.t
module Dump_nativeint : Dump with type a = Nativeint.t
module Dump_int       : Dump with type a = int
module Dump_char      : Dump with type a = char
module Dump_string    : Dump with type a = string
module Dump_float     : Dump with type a = float
module Dump_bool      : Dump with type a = bool
module Dump_unit      : Dump with type a = unit
module Dump_list   (P : Dump) : Dump with type a = P.a list
module Dump_option (P : Dump) : Dump with type a = P.a option

module Dump_undumpable (P : sig type a val tname : string end)
  : Dump with type a = P.a
module Dump_via_marshal (P : sig type a end)
  : Dump with type a = P.a
module Dump_alpha (P : sig type a end)
  : Dump with type a = P.a
