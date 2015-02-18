(* -------------------------------------------------------------------- *)
require import Bool Option Fun Distr Int IntExtra Real NewList Ring.
(*---*) import IterOp.

(* -------------------------------------------------------------------- *)
theory Dlist.
  op distr (n : int) (d : 'a distr) : 'a list distr.

  axiom muE (n : int) (d : 'a distr) (P : 'a -> bool):
      mu (distr n d) (fun s, size s = max n 0 /\ all P s)
    = iterop n Real.( * ) (mu d P) 1%r.

  lemma mu_xE (n : int) (d : 'a distr) s: size s = max n 0 =>
    mu_x (distr n d) s = foldr Real.( * ) 1%r (map (mu_x d) s).
  proof. admit. qed.

  lemma suppE (n : int) (d : 'a distr) s:
        in_supp s (distr n d)
    <=> (size s = max n 0 /\ all (fun x, in_supp x d) s).
  proof. admit. qed.
 
  lemma weightE (n : int) (d : 'a distr):
     weight (distr n d) = (max n 0)%r * (weight d).
  proof. admit. qed.

  lemma lossless (n : int) (d : 'a distr):
    weight d = 1%r => weight (distr n d) = 1%r.
  proof. admit. qed.

  lemma uniform (n : int) (d : 'a distr):
    isuniform d => isuniform (distr n d).
  proof. admit. qed.

  theory Sample.
    type t. op d : t distr.

    module S = {
      proc sample1 (from : int, to : int) : t list = {
        var aout;
        aout = $(distr (to - from) d);
        return aout;
      }
      proc sample2 (from : int, to : int) : t list = {
        var elem = Option.witness;
        var aout = [];

        while (from < to) {
          elem = $d;
          aout = elem :: aout;
          from = from + 1;
        }

        return aout;
      }
    }.
 
    equiv eq_sample: S.sample1 ~ S.sample2 : true ==> ={res}.
    proof. admit. qed.
  end Sample.
end Dlist.
