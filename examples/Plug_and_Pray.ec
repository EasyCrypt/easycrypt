require import Distr.
require import Real.
require import Int.
  import EuclDiv.
require import Pair.

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

axiom bound_pos : bound > 0.

module type Game = {
  fun main(x : tin) : tres
}.

module Guess(G : Game) = {  
  fun main(x : tin) : (int * tres) = {
    var i : int;
    var o : tres;
    o = G.main(x);
    i = $[0..bound - 1];
    return (i,o);
  }
}.

lemma PBound &m (G <: Game):
  forall phi psi x,
       (1%r/bound%r) * Pr[ G.main(x) @ &m: phi (glob G) res ]
     = Pr[ Guess(G).main(x) @ &m: 
           phi (glob G) (snd res) /\
           let k = psi (glob G) (snd res)  in
           fst res = if k >= 0 && k < bound then k else 0 ].
proof strict.
  intros phi psi x_arg.
  bdhoare_deno (_ : (glob G) = (glob G){m} && x_arg = x ==>
                       phi (glob G) (snd res)
                    /\ let k = (psi (glob G) (snd res) ) in
                       fst res = if k >= 0 && k < bound then k else 0) => //.
  fun.
  seq 1 : (phi (glob G) o)
          (Pr[ G.main(x_arg) @ &m: phi (glob G) res ])
          (1%r/bound%r)
          (1%r - Pr[ G.main(x_arg) @ &m: phi (glob G) res ])
          0%r
          (true) => //.
    (* probability equality for 'phi (glob G) o' *)
    call (_ :  (glob G) = (glob G){m} && x = x_arg ==> phi (glob G) res) => //.
    bypr. progress.
    equiv_deno (_ : (glob G){1} = (glob G){2} && x{1} = x{2}
                    ==> (phi (glob G) res){1} = (phi (glob G) res){2}) => //.
      fun true => //.
      by smt.
    (* probability of sampling such that Guess.i = psi (glob G) o *)
    rnd; skip; progress.
    cut W: (lambda (x : int),
              phi (glob G){hr} (snd (x, o{hr})) /\
              fst (x, o{hr}) = (if psi (glob G){hr} (snd (x, o{hr})) >= 0 && psi (glob G){hr} (snd (x, o{hr})) < bound
                               then psi (glob G){hr} (snd (x, o{hr}))
                               else 0))
           =
           ((=)  (if psi (glob G){hr} o{hr} >= 0 && psi (glob G){hr} o{hr} < bound
                  then psi (glob G){hr} o{hr}
                  else 0)).
    by apply fun_ext; rewrite /Fun.(==); smt.
    by rewrite W -/(mu_x _ _) Distr.Dinter.mu_x_def_in; smt.
    (* probability that sampling changes '!phi (glob G) o' to 'phi (glob G) o' zero *)
    rnd. skip. progress.
    cut W:   (lambda (x : int),
                phi (glob G){hr} (snd (x, o{hr})) /\
                fst (x, o{hr}) =
               if psi (glob G){hr} (snd (x, o{hr})) >= 0 &&
                  psi (glob G){hr} (snd (x, o{hr})) < bound
               then  psi (glob G){hr} (snd (x, o{hr})) else 0)
           = cpFalse.
    by apply fun_ext; rewrite /Fun.(==); smt.
    by rewrite W; smt.
qed.