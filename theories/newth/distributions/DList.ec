require import Int Real IntExtra Distr NewDistr NewList.
(*---*) import IterOp.

op distr (n : int) (d : 'a distr) : 'a list distr.

axiom muE (n : int) (d : 'a distr) (P : 'a -> bool):
    mu (distr n d) (fun s, size s = max n 0 /\ all P s)
  = iterop n Real.( * ) (mu d P) 1%r.

lemma mu_xE (n : int) (d : 'a distr) s: size s = max n 0 =>
  mu (distr n d) (pred1 s) = foldr Real.( * ) 1%r (map (fun x => mu d (pred1 x)) s).
proof. admit. qed.

lemma suppE (n : int) (d : 'a distr) s:
      support (distr n d) s
  <=> (size s = max n 0 /\ all (support d) s).
proof. admit. qed.

lemma weightE (n : int) (d : 'a distr):
   mu (distr n d) predT = (max n 0)%r * (mu d predT).
proof. admit. qed.

lemma lossless (n : int) (d : 'a distr):
  is_lossless d => is_lossless (distr n d).
proof. admit. qed.

lemma uniform (n : int) (d : 'a distr):
  is_uniform d => is_uniform (distr n d).
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
