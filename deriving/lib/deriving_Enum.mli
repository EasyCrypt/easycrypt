module type Enum =
  sig
    type a
    val succ : a -> a
    val pred : a -> a
    val to_enum : int -> a
    val from_enum : a -> int
    val enum_from : a -> a list
    val enum_from_then : a -> a -> a list
    val enum_from_to : a -> a -> a list
    val enum_from_then_to : a -> a -> a -> a list
  end

module Defaults
  (E : sig type a val numbering : (a * int) list end)
  : Enum with type a = E.a

module Defaults' 
  (E : sig type a val from_enum : a -> int val to_enum : int -> a end) 
  (B : Deriving_Bounded.Bounded with type a = E.a)
  : Enum with type a = B.a

module Enum_bool : Enum with type a = bool
module Enum_char : Enum with type a = char
module Enum_int  : Enum with type a = int
module Enum_unit : Enum with type a = unit
