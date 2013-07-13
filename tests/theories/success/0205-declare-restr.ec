module type Adv = {
  fun f () : unit
}.

section.

  declare module A : Adv.

  local module M = { var x : int }.

  local module G1 = {
    fun f () : unit = {
      M.x = 1;
      A.f();
    }
  }.

  local module G2 = {
    fun f () : unit = {
      A.f();
      M.x = 1;
    }
  }.

  local equiv foo : G1.f ~ G2.f : ={glob A} ==> true.
  proof.
    fun;swap{1} 1;wp;call (_:true) => //.
  save.
end section.

module M = { var x : int }.

section.

  declare module A : Adv {M}.

  local module G1 = {
    fun f () : unit = {
      M.x = 1;
      A.f();
    }
  }.

  local module G2 = {
    fun f () : unit = {
      A.f();
      M.x = 1;
    }
  }.

  local equiv foo : G1.f ~ G2.f : ={glob A} ==> true.
  proof.
    fun;swap{1} 1;wp;call (_:true) => //.
  save.
end section.