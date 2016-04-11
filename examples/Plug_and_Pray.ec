require import Pair Int IntDiv Real NewDistr.
require import DInterval.

(*
  TODO:
    - Generalize from Dinter to Duni.
    - Provide another version for arbitrary distributions where the
      probability is upper-bounded by maximum probability of element
      in support of distribution.
*)

type tin.
type tres.

const bound : int.

axiom bound_pos : 0 < bound.

module type Game = {
  proc main(x:tin): tres
}.

module Guess(G:Game) = {
  proc main(x:tin): int * tres = {
    var i, o;

    o = G.main(x);
    i = $[0..bound - 1];
    return (i,o);
  }
}.

lemma PBound (G <: Game) phi psi x0 &m:
  (1%r/bound%r) * Pr[G.main(x0) @ &m: phi (glob G) res]
  = Pr[Guess(G).main(x0) @ &m:
         phi (glob G) (snd res) /\
         let k = psi (glob G) (snd res)  in
         fst res = if 0 <= k < bound then k else 0].
proof.
  rewrite eq_sym.
  byphoare (_: (glob G) = (glob G){m} /\ x0 = x ==>
               phi (glob G) (snd res) /\
               let k = psi (glob G) (snd res) in
               fst res = if 0 <= k < bound then k else 0) => //.
  pose p:= Pr[G.main(x0) @ &m: phi (glob G) res].
  proc.
  seq  1: (phi (glob G) o)
          (p) (1%r/bound%r)
          _ 0%r => //.
    (* probability equality for 'phi (glob G) o' *)
    call (_:  (glob G) = (glob G){m} && x = x0 ==> phi (glob G) res) => //.
    bypr; progress; rewrite /p.
    byequiv (_: (glob G){1} = (glob G){2} /\ x{1} = x{2} ==>
                (phi (glob G) res){1} = (phi (glob G) res){2}) => //.
      by proc true.
    smt.
    (* probability of sampling such that Guess.i = psi (glob G) o *)
    rnd; skip; progress.
    rewrite /fst /snd /=.
    cut ->: (fun x,
              phi (glob G){hr} o{hr} /\
              x = if 0 <= psi (glob G){hr} o{hr} < bound
                    then psi (glob G){hr} o{hr}
                    else 0)
            = (pred1  (if 0 <= psi (glob G){hr} o{hr} < bound
                       then psi (glob G){hr} o{hr}
                       else 0)).
      by apply fun_ext=> x //=; rewrite H /= (eq_sym x).
    by rewrite -/(mu_x _ _) mux_dinter; smt.
    (* probability that sampling changes '!phi (glob G) o' to 'phi (glob G) o' zero *)
    hoare; rnd; skip; progress [-split].
    by move: H; rewrite -neqF /snd /= => ->.
qed.
