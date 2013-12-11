module type O = {
  proc o1 () : unit
  proc o2 () : unit
}.

module type Adv(O:O) = {
  proc a () : unit { O.o2 }
}.

module A(O:O) : Adv(O) = {
  proc a () : unit = {
    O.o1();
  }
}.
