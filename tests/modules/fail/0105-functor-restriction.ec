module type O = {
  fun o1 () : unit
  fun o2 () : unit
}.

module type Adv(O:O) = {
  fun a () : unit { O.o2 }
}.

module A(O:O) : Adv(O) = {
  fun a () : unit = {
    O.o1();
  }
}.
