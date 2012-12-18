module type Show =
  sig
    type a
    val format : Format.formatter -> a -> unit
    val format_list : Format.formatter -> a list -> unit
    val show : a -> string
    val show_list : a list -> string
  end

module Defaults (S : 
  sig
    type a
    val format : Format.formatter -> a -> unit 
  end) : Show with type a = S.a

module Show_unprintable (S : sig type a end) : Show with type a = S.a

module Show_char      : Show with type a = char
module Show_bool      : Show with type a = bool
module Show_unit      : Show with type a = unit
module Show_int       : Show with type a = int
module Show_int32     : Show with type a = int32
module Show_int64     : Show with type a = int64
module Show_nativeint : Show with type a = nativeint
module Show_float     : Show with type a = float
module Show_string    : Show with type a = string

module Show_list (S : Show)   : Show with type a = S.a list
module Show_ref (S : Show)    : Show with type a = S.a ref
module Show_option (S : Show) : Show with type a = S.a option
module Show_array (S : Show)  : Show with type a = S.a array

module Show_map
  (O : Map.OrderedType) 
  (K : Show with type a = O.t)
  (V : Show)
  : Show with type a = V.a Map.Make(O).t

module Show_set
  (O : Set.OrderedType) 
  (K : Show with type a = O.t)
  : Show with type a = Set.Make(O).t
