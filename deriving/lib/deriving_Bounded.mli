module type Bounded = 
sig
  type a
  val min_bound : a 
  val max_bound : a 
end

module Bounded_bool      : Bounded with type a = bool
module Bounded_char      : Bounded with type a = char
module Bounded_int       : Bounded with type a = int
module Bounded_int32     : Bounded with type a = int32
module Bounded_int64     : Bounded with type a = int64
module Bounded_nativeint : Bounded with type a = nativeint
module Bounded_unit      : Bounded with type a = unit
module Bounded_open_flag : Bounded with type a = Pervasives.open_flag
module Bounded_fpclass   : Bounded with type a = Pervasives.fpclass
