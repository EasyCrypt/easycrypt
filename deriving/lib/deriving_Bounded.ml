(* Copyright Jeremy Yallop 2007.
   This file is free software, distributed under the MIT license.
   See the file COPYING for details.
*)

(** Primitive instanecs for bounded **)
module Deriving_Bounded = struct
module type Bounded = sig
  type a
  val min_bound : a
  val max_bound : a
end

module Bounded_integer(B : sig type t
                               val max_int : t
                               val min_int : t
                       end) : Bounded with type a = B.t =
struct 
  type a = B.t
  let min_bound = B.min_int
  let max_bound = B.max_int
end
module Bounded_int32 = Bounded_integer(Int32)
module Bounded_int64 = Bounded_integer(Int64)
module Bounded_nativeint = Bounded_integer(Nativeint)
module Bounded_int = struct
  type a = int
  let min_bound = Pervasives.min_int
  let max_bound = Pervasives.max_int
end
module Bounded_bool = struct
  type a = bool
  let min_bound = false
  let max_bound = true
end
module Bounded_char = struct
  type a = char
  let min_bound = Char.chr 0
  let max_bound = Char.chr 0xff (* Is this guaranteed? *)
end
module Bounded_unit = struct
  type a = unit
  let min_bound = ()
  let max_bound = ()
end 
end
include Deriving_Bounded
type open_flag = Pervasives.open_flag  =
                 | Open_rdonly
                 | Open_wronly
                 | Open_append
                 | Open_creat
                 | Open_trunc
                 | Open_excl
                 | Open_binary
                 | Open_text
                 | Open_nonblock
                     deriving (Bounded)

type fpclass = Pervasives.fpclass =
               | FP_normal
               | FP_subnormal
               | FP_zero
               | FP_infinite
               | FP_nan
                   deriving (Bounded)
