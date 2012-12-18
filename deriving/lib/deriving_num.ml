
module Show_num = Deriving_Show.Defaults (struct
  type a = Num.num
  let format formatter item = Format.pp_print_string formatter (Num.string_of_num item)
end)

module Typeable_num    = Deriving_Typeable.Primitive_typeable(struct type t = Num.num let magic = "Primitive.Num.num" end)

module Eq_num : Deriving_Eq.Eq with type a = Num.num =
struct
  type a = Num.num
  let eq = Num.eq_num
end

module Dump_num = Deriving_Dump.Defaults (
  struct
    (* TODO: a less wasteful dumper for nums.  A good start would be
       using half a byte per decimal-coded digit, instead of a whole
       byte. *)
    type a = Num.num
    let to_buffer buffer n = Deriving_Dump.Dump_string.to_buffer buffer (Num.string_of_num n)
    and from_stream stream = Num.num_of_string (Deriving_Dump.Dump_string.from_stream stream)
  end
)



module Pickle_num = Deriving_Pickle.Pickle_from_dump(Dump_num)(Eq_num)(Typeable_num)


