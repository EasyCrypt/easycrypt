module type O = {
  fun o1 () : unit
  fun o2 () : unit
}.

module type Adv1(O:O) = {
  fun a () : unit { O.o1 }
}.

module type Adv2(O:O) = {
  fun a () : unit { O.o2 }
}.

module type Adv12(O:O) = {
  fun a () : unit { O.o1 O.o2 }
}.

module type Adv(O:O) = {
  fun a () : unit 
}.


module A1(O:O) : Adv1(O), Adv12(O) (*, Adv(O) *) = {
  fun a () : unit = {
    O.o1();
  }
}.

module A2(O:O) : Adv2(O), Adv12(O)(*, Adv(O) *)  = {
  fun a () : unit = {
    O.o2();
  }
}.

module A(O:O) : Adv12(O) (*, Adv(O) *) = {
  fun a () : unit = {
    O.o1(); 
    O.o2();
  }
}.




