
module Show_num       : Deriving_Show.Show with type a = Num.num
module Eq_num         : Deriving_Eq.Eq with type a = Num.num
module Typeable_num   : Deriving_Typeable.Typeable with type a = Num.num
module Dump_num       : Deriving_Dump.Dump with type a = Num.num
module Pickle_num     : Deriving_Pickle.Pickle with type a = Num.num

