import why3 "bool" "Bool"
  op "xorb" as "^^".

op xorb(b0:bool, b1:bool):bool = b0 ^^ b1.
