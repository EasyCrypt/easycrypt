module type Adv = {
  proc f () : unit
}.

section.

  declare module A : Adv.

  local module M = { var x : int }.

  local module G1 = {
    proc f () : unit = {
      M.x = 1;
      A.f();
    }
  }.

  local module G2 = {
    proc f () : unit = {
      A.f();
      M.x = 1;
    }
  }.

  local equiv foo : G1.f ~ G2.f : ={glob A} ==> true.
  proof -strict.
    proc;swap{1} 1;wp;call (_:true) => //.
  qed.
end section.

module M = { var x : int }.

section.

  declare module A : Adv {M}.

  local module G1 = {
    proc f () : unit = {
      M.x = 1;
      A.f();
    }
  }.

  local module G2 = {
    proc f () : unit = {
      A.f();
      M.x = 1;
    }
  }.

  local equiv foo : G1.f ~ G2.f : ={glob A} ==> true.
  proof -strict.
    proc;swap{1} 1;wp;call (_:true) => //.
  qed.
end section.