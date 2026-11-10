(* cond_l: the conditioning rule must reject an observation that reads the
   observed variable. Without the side condition, the derivation below went
   through and produced the false `equiv bad`; combined with
   Pr[p1 : z = 1] = 1/2 and Pr[p2 : z = 1] = 0 it proved `false`. *)
require import AllCore List Distr.

module M = {
  var x, y, z : int
  proc p1() = { x <$ duniform [0; 1]; y <- y + x; z <- x; }
  proc p2() = { x <$ duniform [0; 1]; y <- y + x; z <- 0; }
}.

equiv bad : M.p1 ~ M.p2 : ={M.y} ==> ={M.z}.
proof.
proc. delay.
dcoupl seq 1 1 (={M.y}) with (M.x <$ duniform [0; 1]; ~ M.x <$ duniform [0; 1];);
  first by dcoupl push {1}; dcoupl push {2}; dcoupl skip.
dcoupl seq 1 1 (={M.y})
  with (M.x <$ dcond (duniform [0; 1]) (fun v => M.y + v = M.y); ~
        M.x <$ dcond (duniform [0; 1]) (fun v => M.y + v = M.y);).
fail dcoupl cond {1}.
admit. admit.
qed.
