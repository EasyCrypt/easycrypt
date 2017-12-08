require import AllCore Distr DBool DInterval List.

require BitWord Bigop.

clone import BitWord as BS.
clone import Bigop as BBS with
   type t <- BS.word,
   op Support.idm <- BS.zerow,
   op Support.( + ) <- BS.(+^)
   proof * by smt.

op N:int.

pred sxor (s s':int list) (i:int) =
  exists s1 s2, s = s1 ++ s2 /\ s' = s1 ++ i :: s2.

pred sxor2 (s s':int list) (i:int) =
  sxor s s' i \/ sxor s' s i.

lemma sxor_cons s i : sxor s (i :: s) i.
proof. by exists [] s. qed.

lemma sxor2_cons (s s':int list) (i j:int):
  sxor2 s s' i => sxor2 (j::s) (j::s') i.
proof. smt []. qed.

(* The database *)
op a : int -> word.

module PIR = {

  proc query (s:int list) = {
    return (big predT a s);
  } 

  var s, s' : int list

  proc main (i:int) = {
    var r, r' : word;
    var j = 0;

    var b;

    (s, s') = ([], []);
    while (j < N) {
      b <$ {0,1};
      if (j = i) {
        if (b) s <- j :: s; else s' <- j :: s';
      } else {
        if (b) { s <- j :: s; s' <- j :: s'; }
      }
      j <- j + 1;
    }

    r <@ query(s);
    r' <@ query(s');

    return r +^ r';
  }
   
}.

lemma PIR_correct &m i0 : 0 <= i0 < N => Pr [PIR.main(i0) @ &m : res = a i0] = 1%r.
proof.
  move=> bound.
  (* TODO: allows to do directly "byhoare (_: i = i0 ==> res = a i0)" *)
  byphoare (_: i = i0 ==> res = a i0) => // {&m}.
  conseq (: _ ==> true) (: _ ==> res = a i0)=> //.
  + proc;inline *;wp.
    conseq (_: _ ==> sxor2 PIR.s PIR.s' i) => //.
    + by move=> &m -> s s' [] [s1 s2 [-> ->]];rewrite !big_cat big_consT;ring.
    while (j <= N /\ if j <= i then PIR.s = PIR.s' else sxor2 PIR.s PIR.s' i).
    + wp;rnd;skip => /= &m [[_]] + HjN. 
      have -> /= : j{m} + 1 <= N by smt [].
      case: (j{m} <= i{m}) => Hji;2: by smt [].
      move=> -> b _;case: (j{m} = i{m}) => [->> | /#].
      by rewrite (_ : !(i{m}+1 <= i{m})) 1:/# /=; smt w=sxor_cons.
    by auto => /#.
  proc;inline *;wp.
  while (true) (N-j).
  + move=> z;wp;rnd predT;skip => &hr />;smt w=dbool_ll.
  by auto=> /#. 
qed.

equiv PIR_secure1: PIR.main ~ PIR.main : true ==> ={PIR.s}.
proof.
  proc;inline *;wp.
  while (={j,PIR.s});auto.
qed.

equiv PIR_secure2: PIR.main ~ PIR.main : true ==> ={PIR.s'}.
proof.
  proc;inline *;wp.
  while (={j,PIR.s'});2: by auto.
  case: ((j = i){1}).
  + rcondt{1} 2; 1:by auto.
    case: ((j = i){2}); 1: by rcondt{2} 2; auto.
    rcondf{2} 2; 1:by auto.  
    wp;rnd (fun x => !x);skip => &m1 &m2 /> ??; split=>[??| _ b _];1:by apply dbool_funi.
    by apply dbool_fu.
  rcondf{1} 2; 1:by auto.
  case: ((j = i){2}); 2: by rcondf{2} 2; auto.
  rcondt{2} 2; 1: by auto.
  wp;rnd (fun x => !x);skip => &m1 &m2 /> ??; split=>[??| _ b _];1:by apply dbool_funi.
  by apply dbool_fu.
qed.
