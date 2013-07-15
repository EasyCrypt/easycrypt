module type Adv = {
  fun f () : unit
}.

module M = { var x : int }.

section.

  declare module A : Adv.

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
    fun;swap{1} 1.
    admit.
  save.
end section.