(* -------------------------------------------------------------------- *)
require import AllCore List Distr Ring StdBigop StdRing StdOrder.
(*---*) import IntID Bigreal Bigreal.BRM.

pragma +implicits.

(* ==================================================================== *)
abstract theory JoinSampling.
type ta.

module S = {
  proc sample(ds : ta distr list): ta list = {
    var rs;

    rs <$ djoin ds;
    return rs;
  }

  proc loop(ds : ta distr list): ta list = {
    var i, r, l;

    i <- size ds - 1;
    l <- [];
    while (0 <= i) {
      r <$ (nth witness ds i);
      l <- r :: l;
      i <- i - 1;
    }
    return l;
  }
}.

(* -------------------------------------------------------------------- *)
lemma pr_sample ds0 &m xs:
  Pr[S.sample(ds0) @ &m: res = xs] = mu (djoin ds0) (pred1 xs).
proof. by byphoare (_: ds = ds0 ==> res = xs)=> //=; proc; rnd. qed.

end JoinSampling.

(* ==================================================================== *)
abstract theory JoinMapSampling.

type ta, tb.

module S = {
  proc sample(d: ta -> tb distr, xs: ta list): tb list = {
    var r;
  
    r <$ djoinmap d xs;
    return r;
  }

  proc loop(d: ta -> tb distr, xs: ta list): tb list = {
    var i, r, l;

    i <- size xs - 1;
    l <- [];
    while (0 <= i) {
      r <$ d (nth witness xs i);
      l <- r :: l;
      i <- i - 1;
    }
    return l;
  }

  proc loop_first(d: ta -> tb distr, xs: ta list): tb list = {
    var r, l;

    l <- [];
    while (xs<>[]) {
      r <$ d (head witness xs);
      l <- rcons l r;
      xs <- behead xs;
    }
    return l;
  }

}.

equiv Sample_Loop_eq: S.sample ~ S.loop: ={d, xs} ==> ={res}.
proof. 
  proc => /=; alias{1} 1 rb = witness <:tb>.
  sp 1 2; exlim xs{1}, l{2} => xs_ l2.
  pose xs' := List."[]" <:ta>.
  conseq (: ={d} /\ l{2} = l2 /\ i{2} = size xs_ - 1 /\ xs{1} = xs_ /\ xs{2} = xs_ ++ xs'
             ==> r{1} ++ l2 = l{2}); 1,2: by move=> />; smt(cats0).
  elim/last_ind: xs_ xs' l2 => [ | xs_ x hrec] xs' l2.
  + rcondf{2} ^while; 1: by auto.
    rnd{1}; skip => />; split; 1: by apply djoin_ll.
    by move=> _ ?; rewrite djoin_nil => /supp_dunit.
  rcondt{2} ^while; 1: by auto => />; rewrite size_rcons /= size_ge0. 
  transitivity{1} { rb <$ (d x);
                    xs <- xs_;
                    r <$ djoinmap d xs;
                    r <- rcons r rb; }
    (={d,xs} /\ xs{1} = rcons xs_ x ==> ={r})
    (={d} /\ l{2} = l2 /\ i{2} = size (rcons xs_ x) - 1 /\ xs{1} = rcons xs_ x /\ xs{2} = rcons xs_ x ++ xs'
     ==> r{1} ++ l2 = l{2}) => //; 1: smt().
  + rndsem{2} 0; rnd (fun (r: tb list) => (last witness r, xs_, r)) (fun p:_ * _ * _ => p.`3).
    skip => /> &2; split => [ | _].
    + by move=> p /supp_dlet /= [rb [_ /supp_dmap [rbs [_ -> /=]]]]; rewrite last_rcons.
    split => [ | _].
    + move=> p /supp_dlet /= [rb [_ /supp_dmap [rbs [_ -> /=]]]].
      rewrite map_rcons djoin_rcons dmap_dprodE_swap /=.
      rewrite 2!dlet1E; congr; apply fun_ext => rb'; congr => /=.
      rewrite /dmap 2!dlet1E; congr; apply fun_ext => r'; congr => /=.
      rewrite !dunit1E /=; smt(rconssI rconsIs).
    rewrite map_rcons djoin_rcons dmap_dprodE_swap /= => rb /supp_dlet /=[ra [hra]].
    move=> /supp_dmap /= [rb' [hrb']] ->; rewrite last_rcons.
    by apply/supp_dlet; exists ra; rewrite hra /=; apply supp_dmap; exists rb'.
  wp; seq 2 3 : (={d} /\ rb{1} = r{2} /\
                 l{2} = r{2} :: l2 /\
                 i{2} = size xs_ - 1 /\ xs{1} = xs_ /\ xs{2} = xs_ ++ x::xs').
  + by wp; rnd; skip => /> &2; rewrite cat_rcons /= size_rcons /= nth_cat.
  exlim r{2} => r2; wp.
  by conseq (hrec (x::xs') (r2::l2)) => /> *; rewrite cat_rcons.
qed.

equiv Sample_Loop_first_eq: S.sample ~ S.loop_first : ={d, xs} ==> ={res}.
proof. 
  proc => /=;  alias{1} 1 rb = witness <:tb>.
  sp 1 1; exlim xs{1}, l{2} => xs_ l2.
  conseq (: ={d,xs} /\ l{2} = l2 /\ xs{2} = xs_ 
             ==> l2++r{1} = l{2}); 1,2: by move=> />.
  elim: xs_ l2 => [ | x xs_ hrec] l2.
  + rcondf{2} ^while; 1: by auto.
    rnd{1}; skip => />; split; 1: by apply djoin_ll.
    by move=> _ ?; rewrite djoin_nil => /supp_dunit ->; rewrite cats0.
  rcondt{2} ^while; 1: by auto.
  transitivity{1} { rb <$ (d x);
                    xs <- xs_;
                    r <$ djoinmap d xs;
                    r <- rb :: r; }
    (={d,xs} /\ xs{1} = x :: xs_ ==> ={r})
    (={d, xs} /\ l{2} = l2 /\  xs{2} = x :: xs_ ==> l2++r{1} = l{2}) => //; 1: smt().
  + rndsem{2} 0; rnd (fun (r: tb list) => (head witness r, xs_, r)) (fun p:_ * _ * _ => p.`3).
    skip => /> &2; split => [ | _].
    + by move=> p /supp_dlet /= [rb [_ /supp_dmap [rbs [_ -> /=]]]].
    split => [ | _].
    + move=> p /supp_dlet /= [rb [_ /supp_dmap [rbs [_ -> /=]]]].
      rewrite djoin_cons /= dmap1E dprod_dlet.
      rewrite dlet1E dletE; congr; apply fun_ext => rb' /=; congr.
      rewrite dlet1E dletE; congr; apply fun_ext => r' /=; congr.
      rewrite /(\o) /= !dunitE /pred1 /= /#.
    rewrite djoin_cons /= => rs /supp_dmap [[b bs]] /= [] /supp_dprod /= [] ?? -> /=.
    apply/supp_dlet; exists b; split => //=.
    by apply/supp_dmap; exists bs.
  wp; seq 2 3 : (={d, xs} /\ l{2} = rcons l2 r{2} /\ xs{2} = xs_ /\ rb{1} = r{2}).
  + by wp; rnd; skip => /> &2.
  exlim r{2} => r2; wp.
  by conseq (hrec (rcons l2 r2)) => /> *; rewrite cat_rcons.
qed.

end JoinMapSampling.
