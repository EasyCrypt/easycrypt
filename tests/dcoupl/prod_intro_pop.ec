(* Exercise Prod_L intro after popping two samples from the body
   into R. The final judgment has R_l = product sample, body empty,
   S empty.                                                         *)
require import AllCore Distr DBool DProd.

module M = {
  var x : bool
  var y : bool

  proc f() : bool * bool = {
    M.x <$ {0,1};
    M.y <$ {0,1};
    return (M.x, M.y);
  }
  proc g() : bool * bool = {
    M.x <$ {0,1};
    M.y <$ {0,1};
    return (M.x, M.y);
  }
}.

(* Verify Prod_L intro fires after pop 2 — the goal ends in a product
   sample on each R side. We admit to close since the remaining goal
   isn't expressible as simple Skip/Rnd. *)
lemma prod_intro_pop : equiv[ M.f ~ M.g : true ==> true ].
proof.
proc. delay.
dcoupl pop 2.
dcoupl prod intro.      (* combine R_l's two samples into a product *)
dcoupl prod intro {2}.  (* same for R_r *)
admit.
qed.
