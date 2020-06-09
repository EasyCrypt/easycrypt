require import AllCore List Distr Dexcepted PKE.
require import StdOrder StdBigop.
import RField RealOrder Bigreal.

require TCR RndExcept.

(** DiffieHellman *)
require import DiffieHellman.
import DDH.

axiom gt1_q : 1 < q.

theory Ad1.

  clone import RndExcept as RndE with
    type input <- unit,
    type t     <- F.t,
    op   d     <- fun _ => FDistr.dt,
    type out   <- bool
    proof *. 
    realize d_ll. move=> _;apply FDistr.dt_ll. qed.
  
  clone include Adversary1_1 with
    op n <- q
    proof *.
  realize gt1_n by apply gt1_q.
  realize d_uni by move=> _ x; rewrite FDistr.dt1E.

end Ad1.

theory DDH_ex.

  module DDH0_ex (A:Adversary) = {
    proc main() : bool = {
      var b, x, y;
      x <$ FDistr.dt \ (pred1 F.zero);
      y <$ FDistr.dt;
      b <@ A.guess(g ^ x, g ^ y, g ^ (x*y));
      return b;
    }
  }.

  module DDH1_ex (A:Adversary) = {
    proc main() : bool = {
      var b, x, y, z;

      x <$ FDistr.dt \ (pred1 F.zero);
      y <$ FDistr.dt;
      z <$ FDistr.dt;
      b <@ A.guess(g ^ x, g ^ y, g ^ z);
      return b;
    }
  }.

  section PROOFS.

  declare module A:Adversary.  

  axiom A_ll : islossless A.guess.

  local module Addh0 : Ad1.ADV = {
    proc a1 () = { return ((), F.zero); }
    proc a2 (x:t) = {
      var b, y;
      y <$ FDistr.dt;
      b <@ A.guess(g ^ x, g ^ y, g ^ (x*y));
      return b;
    }
  }.

  local module Addh1 = {
    proc a1 = Addh0.a1
    proc a2 (x:t) = {
      var b, y, z;
      y <$ FDistr.dt;
      z <$ FDistr.dt;
      b <@ A.guess(g ^ x, g ^ y, g ^ z);
      return b;
    }
  }.

  local lemma a1_ll : islossless Addh0.a1.
  proof. proc;auto. qed.

  lemma adv_DDH_DDH_ex &m :
     `| Pr[DDH0_ex(A).main()@ &m : res] - Pr[DDH1_ex(A).main()@ &m : res] | <=
     `| Pr[DDH0(A).main()@ &m : res] - Pr[DDH1(A).main()@ &m : res] | + 2%r / q%r.
  proof.
    have /= H0 := Ad1.pr_abs Addh0 a1_ll _ &m (fun b _ => b).      
    + by proc;call A_ll;rnd;skip;rewrite /= FDistr.dt_ll.
    have /= H1 := Ad1.pr_abs Addh1 a1_ll _ &m (fun b _ => b). 
    + by proc;call A_ll;do !rnd;skip;rewrite /= FDistr.dt_ll.
    have -> : 2%r / q%r = inv q%r + inv q%r. 
    + field;smt (q_pos lt_fromint).
    have <- : Pr[Ad1.MainE(Addh0).main() @ &m : res] = Pr[DDH0_ex(A).main() @ &m : res].
    + by byequiv => //;proc;inline *;sim;auto.
    have <- : Pr[Ad1.MainE(Addh1).main() @ &m : res] = Pr[DDH1_ex(A).main() @ &m : res].
    + by byequiv => //;proc;inline *;sim;auto.
    have <- : Pr[Ad1.Main(Addh0).main() @ &m : res] = Pr[DDH0(A).main() @ &m : res].
    + by byequiv => //;proc;inline *;sim;auto.
    have <- /# : Pr[Ad1.Main(Addh1).main() @ &m : res] = Pr[DDH1(A).main() @ &m : res].
    by byequiv => //;proc;inline *;sim;auto.
  qed.

  end section PROOFS.

end DDH_ex.
import DDH_ex.

(** Target Collision Resistant *)

clone import TCR as TCR_H with 
  type t_from <- group * group * group,
  type t_to   <- F.t.

axiom dk_ll : is_lossless dk.
hint exact random : dk_ll.

(** Cramer Shoup Encryption *)

clone import PKE as PKE_ with
   type pkey = K * group * group * group * group * group,
   type skey = K * group * group * F.t * F.t * F.t * F.t * F.t * F.t,
   type plaintext = group,
   type ciphertext = group * group * group * group.

module CramerShoup : Scheme = {
  proc kg() : pkey * skey = {
    var x1, x2, y1, y2, z1, z2, k, w, g_, pk, sk;
    x1 <$ FDistr.dt;
    x2 <$ FDistr.dt;
    y1 <$ FDistr.dt;
    y2 <$ FDistr.dt;
    z1 <$ FDistr.dt;
    z2 <$ FDistr.dt;
    w  <$ FDistr.dt \ (pred1 F.zero);
    k  <$ dk;
    g_ <- g ^ w;
    pk <- (k, g, g_, g^x1 * g_^x2, g^y1 * g_^y2, g^z1 * g_^z2);
    sk <- (k, g, g_, x1, x2, y1, y2, z1, z2);
    return (pk, sk);
  }

  proc enc(pk:pkey, m:plaintext) : ciphertext = {
    var k,g,g_,e,f,h,u,a,a_,c,v,d;
    (k,g,g_,e,f,h) <- pk;
    u <$ FDistr.dt;
    a <- g^u; a_ <- g_^u;
    c <- h^u * m;
    v <- H k (a, a_, c);
    d <- e^u * f^(u*v);
    return (a,a_,c,d);
  } 

  proc dec(sk:skey, ci:ciphertext) = {
    var k,g,g_,x1,x2,y1,y2,z1,z2,a,a_,c,d,v;
    (k,g,g_,x1,x2,y1,y2,z1,z2) <- sk;
    (a,a_,c,d) <- ci;
    v <- H k (a, a_, c);
    return (if d = a ^ (x1 + v * y1) * a_^(x2 + v * y2) then Some (c / (a^z1 * a_^z2))
            else None);
  }

}.

(** Correctness of the scheme *)

hoare CramerShoup_correct : Correctness(CramerShoup).main : true ==> res.
proof.
  proc;inline *;auto => /> &m1 x1 _ x2 _ y1 _ y2 _ z1 _ z2 _ w Hw k _ u _.
  have -> /=: (g ^ x1 * g ^ w ^ x2) ^ u *
    (g ^ y1 * g ^ w ^ y2) ^
    (u * H k (g ^ u, g ^ w ^ u, (g ^ z1 * g ^ w ^ z2) ^ u * m{m1})) =
    g ^ u ^
    (x1 + H k (g ^ u, g ^ w ^ u, (g ^ z1 * g ^ w ^ z2) ^ u * m{m1}) * y1) *
    g ^ w ^ u ^
    (x2 + H k (g ^ u, g ^ w ^ u, (g ^ z1 * g ^ w ^ z2) ^ u * m{m1}) * y2).
  + by rewrite log_bij !(log_g, log_pow, log_mul);ring.
  by rewrite log_bij -div_def !(log_g, log_pow, log_mul);ring.
qed.

(** IND-CCA Security of the scheme *)

module B_DDH (A:CCA_ADV) = {

  module CCA = CCA(CramerShoup, A)

  proc guess(gx gy gz:group): bool = {
    var g_, a, a_, x1,x2,y1,y2,z1,z2,k,e,f,h,m0,m1,b,b',c,v,d,c',pk;
    x1 <$ FDistr.dt;
    x2 <$ FDistr.dt;
    y1 <$ FDistr.dt;
    y2 <$ FDistr.dt;
    z1 <$ FDistr.dt;
    z2 <$ FDistr.dt;
    g_ <- gx;
    a  <- gy;
    a_ <- gz;
    k  <$ dk;
    e  <- g^x1 * g_^x2;
    f  <- g^y1 * g_^y2;
    h  <- g^z1 * g_^z2;
    CCA.log <- [];
    CCA.cstar <- None;
    pk <- (k, g, g_, g^x1 * g_^x2, g^y1 * g_^y2, g^z1 * g_^z2);
    CCA.sk <- (k, g, g_, x1, x2, y1, y2, z1, z2);
    (m0,m1) <- CCA.A.choose(pk);
    b <$ {0,1};
    c <- a^z1 * a_^z2 * (b ? m1 : m0);
    v <- H k (a,a_,c);
    d <- a^(x1 + v*y1) * a_^(x2+v*y2);
    c' <- (a,a_,c,d);
    CCA.cstar <- Some c';
    b' <- CCA.A.guess(c');
    return (b = b');
  }
    
}.

 module B_TCR (A:CCA_ADV) = {
    var log   : ciphertext list
    var cstar : ciphertext option
    var g3    : ( group * group * group) option
    var g_, a, a_, c, d : group
    var w, u , u', x, y, z, alpha, v' : t
    var k : K
    module O = {
      proc dec(ci:ciphertext) = {
        var m, a,a_,c,d,v;
        m <- None;
        if (size log < PKE_.qD && Some ci <> cstar) {
          log <- ci :: log;
          (a,a_,c,d) <- ci;
          v <- H k (a, a_, c);
          if (a_ <> a^w /\ v = v' /\ (a,a_,c) <> (B_TCR.a, B_TCR.a_,B_TCR.c)) g3 <- Some (a,a_,c);
          m <- if (a_ = a^w /\ d = a ^ (x + v*y)) then Some (c / a ^ z)
              else None;
        }
        return m;
      }
    }

    module A = A (O)

    proc c1() = {
      var r';
      log <- [];
      g3 <- None;
      cstar <- None;
      w <$ FDistr.dt \ (pred1 F.zero);
      u <$ FDistr.dt; 
      u' <$ FDistr.dt \ (pred1 u);
      g_ <- g ^ w; 
      a <- g^u; a_ <- g_^u';
      r' <$ FDistr.dt; c <- g^r';
      return (a, a_, c);
    }
    
    proc c2 (k:K) = {
      var m0, m1, b0, e, f, h, r;
      B_TCR.k <- k;
      y <$ FDistr.dt; f <- g^y;
      z <$ FDistr.dt; h <- g^z;      
      v' <- H k (a, a_, c);
      x <$ FDistr.dt; r <$ FDistr.dt; e <- g^x;
      alpha <- (r - u*(x + v'*y))/ (w*(u'-u));
      d <- g ^ r;
      (m0,m1) <@ A.choose(k, g, g_, e, f, h); 
      cstar <- Some (a,a_,c,d);
      b0 <@ A.guess(a,a_,c,d);
      return (oget g3);    
    }
  }.

lemma CCA_dec_ll (A<:CCA_ADV) : islossless CCA(CramerShoup, A).O.dec.
proof. islossless. qed.

section Security_Aux.

  declare module A : CCA_ADV {CCA, B_TCR}.
  axiom guess_ll : forall (O <: CCA_ORC{A}), islossless O.dec => islossless A(O).guess.
  axiom choose_ll : forall (O <: CCA_ORC{A}), islossless O.dec => islossless A(O).choose.

  equiv CCA_DDH0 : CCA(CramerShoup, A).main ~ DDH0_ex(B_DDH(A)).main : ={glob A} ==> ={res}.
  proof.   
    proc;inline *;wp.
    call (_: ={glob CCA}); 1: sim.
    swap{1} 9 -8; swap{1} 20 -18; auto.
    call (_: ={glob CCA}); 1: sim.
    auto => &m1 &m2 /> w _ u _ x1 _ x2 _ y1 _ y2 _ z1 _ z2 _ k _ r b _.
    have -> : 
      H k
       (g ^ u, g ^ w ^ u,
        (g ^ z1 * g ^ w ^ z2) ^ u * if b then r.`2 else r.`1) =
      H k
       (g ^ u, g ^ (w * u),
        g ^ u ^ z1 * g ^ (w * u) ^ z2 * if b then r.`2 else r.`1).
    + by congr;congr;rewrite log_bij !(log_g, log_pow, log_mul); ring.
    progress;
      try by (rewrite log_bij !(log_g, log_pow, log_mul);ring).
    smt ().
  qed.

  lemma pr_CCA_DDH0 &m : 
    Pr[CCA(CramerShoup, A).main() @ &m : res] = 
    Pr[DDH0_ex(B_DDH(A)).main() @ &m : res].
  proof. by byequiv CCA_DDH0. qed.

  local module G1 = {
    var log     : ciphertext list
    var cstar   : ciphertext option
    var bad     : bool
    var u,u',w  : t
    var x,x1,x2 : t
    var y,y1,y2 : t
    var z,z1,z2 : t
    var g_: group
    var k       : K

    module O = {
      proc dec(ci:ciphertext) = {
        var m, a,a_,c,d,v;
        m <- None;
        if (size log < PKE_.qD && Some ci <> G1.cstar) {
          log <- ci :: log;
          (a,a_,c,d) <- ci;
          v <- H k (a, a_, c);
          bad <- bad \/ (a_ <> a^w /\ d = a ^ (x1 + v*y1) * a_ ^ (x2 + v * y2));
          m <- if (a_ = a^w /\ d = a ^ (x + v*y)) then Some (c / a ^ z)
              else None;
        }
        return m;
      }
    }

    module A = A(O)

    proc a1 () = {
      log <- [];
      cstar <- None;
      bad <- false;
      w <$ FDistr.dt \ (pred1 F.zero);
      u <$ FDistr.dt; 
      return ((),u);
    }

    proc a2 (u0' : t) = {
      var m0, m1, b, b0, a, a_, c, d, v, e, f, h;
      u' <- u0';
      g_ <- g ^ w; k  <$ dk;
      a <- g^u; a_ <- g_^u';
      x <$ FDistr.dt; x2 <$ FDistr.dt; x1 <- x - w * x2; e <- g^x;
      y <$ FDistr.dt; y2 <$ FDistr.dt; y1 <- y - w * y2; f <- g^y;
      z <$ FDistr.dt; z2 <$ FDistr.dt; z1 <- z - w * z2; h <- g^z;
      (m0,m1) <@ A.choose(k, g, g_, e, f, h); 
      b <$ {0,1}; 
      c <- a^z1 * a_^z2 * (b ? m1 : m0);
      v <- H k (a, a_, c);
      d <- a^(x1 + v*y1) * a_^(x2+v*y2);
      cstar <- Some (a,a_,c,d);
      b0 <@ A.guess(a,a_,c,d);
      return (b = b0);
    }
  }.

  local equiv DDH1_G1_dec : 
    CCA(CramerShoup, A).O.dec ~ G1.O.dec : 
    ( !G1.bad{2} /\ c{1} = ci{2} /\
      (G1.x{2} = G1.x1{2} + G1.w{2} * G1.x2{2} /\
       G1.y{2} = G1.y1{2} + G1.w{2} * G1.y2{2} /\
       G1.z{2} = G1.z1{2} + G1.w{2} * G1.z2{2}) /\
       CCA.log{1} = G1.log{2} /\ CCA.cstar{1} = G1.cstar{2} /\
       CCA.sk{1} = (G1.k{2}, g, G1.g_{2}, G1.x1{2}, G1.x2{2}, G1.y1{2}, G1.y2{2}, G1.z1{2}, G1.z2{2})) ==>
    (!G1.bad{2} =>
       ={res} /\
       (G1.x{2} = G1.x1{2} + G1.w{2} * G1.x2{2} /\
        G1.y{2} = G1.y1{2} + G1.w{2} * G1.y2{2} /\
        G1.z{2} = G1.z1{2} + G1.w{2} * G1.z2{2}) /\
       CCA.log{1} = G1.log{2} /\ CCA.cstar{1} = G1.cstar{2} /\
       CCA.sk{1} = (G1.k{2}, g, G1.g_{2}, G1.x1{2}, G1.x2{2}, G1.y1{2}, G1.y2{2}, G1.z1{2}, G1.z2{2})).
  proof.
    proc;sp 0 1;inline *;if => //;auto.
    move=> &m1 &m2 /> _ /=;rewrite negb_and /=.
    case: (ci{m2}) => a a_ c d => /=.
    case: (a_ = a ^ G1.w{m2}) => [ -> _ _ | _ _ _ -> ] //=.
    have -> : 
      a ^ (G1.x1{m2} + H G1.k{m2} (a, a ^ G1.w{m2}, c) * G1.y1{m2}) *
      a ^ G1.w{m2} ^ (G1.x2{m2} + H G1.k{m2} (a, a ^ G1.w{m2}, c) * G1.y2{m2}) =
      a ^ (G1.x1{m2} + G1.w{m2} * G1.x2{m2} +
           H G1.k{m2} (a, a ^ G1.w{m2}, c) * (G1.y1{m2} + G1.w{m2} * G1.y2{m2})).
    + by rewrite log_bij !(log_g, log_pow, log_mul);ring.
    have -> // : a ^ G1.z1{m2} * a ^ G1.w{m2} ^ G1.z2{m2} =
                 a ^ (G1.z1{m2} + G1.w{m2} * G1.z2{m2}).
    by rewrite log_bij !(log_g, log_pow, log_mul);ring.
  qed.

  local lemma G1_dec_ll : islossless G1.O.dec. 
  proof. by proc;inline *;auto. qed.

  local lemma G1_dec_bad : phoare[ G1.O.dec : G1.bad ==> G1.bad ] = 1%r.
  proof. by proc; auto => ? ->. qed.

  local equiv DDH1_G1 : DDH1_ex(B_DDH(A)).main ~ Ad1.Main(G1).main : 
                        ={glob A} ==> !G1.bad{2} => ={res}.
  proof.
    proc;inline *;wp.
    call (_: G1.bad, 
             (
              (G1.x = G1.x1 + G1.w * G1.x2 /\
               G1.y = G1.y1 + G1.w * G1.y2 /\
               G1.z = G1.z1 + G1.w * G1.z2){2} /\
              CCA.log{1} = G1.log{2} /\ CCA.cstar{1} = G1.cstar{2} /\ 
              CCA.sk{1} = (G1.k, g, G1.g_, G1.x1, G1.x2, G1.y1, G1.y2, G1.z1, G1.z2){2})).
      + by apply guess_ll.
      + by apply DDH1_G1_dec.
      + by move=> _ _; apply (CCA_dec_ll A).
      + by move=> _;apply G1_dec_bad.
    wp;rnd.
    call (_: G1.bad, 
             (
              (G1.x = G1.x1 + G1.w * G1.x2 /\
               G1.y = G1.y1 + G1.w * G1.y2 /\
               G1.z = G1.z1 + G1.w * G1.z2){2} /\
              CCA.log{1} = G1.log{2} /\ CCA.cstar{1} = G1.cstar{2} /\ 
              CCA.sk{1} = (G1.k, g, G1.g_, G1.x1, G1.x2, G1.y1, G1.y2, G1.z1, G1.z2){2})).
      + by apply choose_ll.
      + by apply DDH1_G1_dec.
      + by move=> _ _; apply (CCA_dec_ll A).
      + by move=> _;apply G1_dec_bad.
    swap{1} 16 -9;wp.
    swap -1;rnd (fun z => z + G1.w{2} * G1.z2{2}) (fun z => z - G1.w{2} * G1.z2{2}).
    rnd;wp.
    swap -1;rnd (fun z => z + G1.w{2} * G1.y2{2}) (fun z => z - G1.w{2} * G1.y2{2}).
    rnd;wp.
    swap -1;rnd (fun z => z + G1.w{2} * G1.x2{2}) (fun z => z - G1.w{2} * G1.x2{2}).
    rnd;wp;rnd;wp.
    rnd (fun z => z / x{1}) (fun z => z * x{1}) => /=.
    auto => &m1 &m2 /= -> xL H;rewrite H /=;move: H => /supp_dexcepted. 
    rewrite /pred1 -ofint0 => -[] InxL HxL yL _.
    split => [ ? _ | eqxL]; 1:by field. 
    move=> zL InzL_; split => [ | _]; 1:by field. 
    move=> kL -> /= x2L _.
    split => [ ? _ | Eqx2L]; 1: by ring.
    move=> x1L Inx1L;split; 1: by ring.
    move=> _ y2L _ /=;split => [ ? _ | Eqy2L]; 1: by ring.
    move=> y1L Iny1L; split => [ | H{H}]; 1: by ring.
    move=> z2L _ /=;split => [ ? _ | Eqz2L]; 1: by ring.
    move=> z1L Inz1L. 
    have <- /= : z1L = z1L + xL * z2L - xL * z2L by ring. 
    have H1 : forall x1L x2L, g ^ x1L * g ^ xL ^ x2L = g ^ (x1L + xL * x2L).
    + by move=> ??;rewrite log_bij !(log_g, log_pow, log_mul);ring.
    rewrite !H1 /=.
    have H2 : forall x1L x2L, x1L + xL * x2L = x1L + xL * x2L - xL * x2L + xL * x2L.
    +  by move=> ??;ring.
    rewrite -!H2 /=;split=> [ | _].
    + by split ;ring.
    move=> ??????? Hbad ? ? /=.
    have <- /= : g ^ zL = g ^ xL ^ (zL / xL).
    + by rewrite log_bij !(log_g, log_pow, log_mul);field.
    split.
    + move=> /Hbad [#] !->> /= <- <-.
      by split; rewrite log_bij !(log_g, log_pow, log_mul) /=.
    by move=> _ {H Hbad} ??????? Hbad /Hbad.
  qed.

  lemma dt_r_ll x : is_lossless (FDistr.dt \ pred1 x).
  proof. 
    by rewrite dexcepted_ll ?FDistr.dt_ll // FDistr.dt1E ltr_pdivr_mulr /= lt_fromint; smt (gt1_q).
  qed.
  
  local lemma aux1 &m : 
    Pr[CCA(CramerShoup, A).main() @ &m : res] <= 
       `| Pr[DDH0(B_DDH(A)).main() @ &m : res] - Pr[DDH1(B_DDH(A)).main() @ &m : res] | 
    + Pr[Ad1.MainE(G1).main() @ &m : res \/ G1.bad] + 3%r/q%r.
  proof.
    have -> : 
     Pr[CCA(CramerShoup, A).main() @ &m : res] = Pr[DDH0_ex(B_DDH(A)).main() @ &m : res].
    + byequiv CCA_DDH0 => //.
    have := adv_DDH_DDH_ex (B_DDH(A)) _ &m.
    + proc;call (guess_ll (<:CCA(CramerShoup,A).O) (CCA_dec_ll A));auto.
      call (choose_ll (<:CCA(CramerShoup,A).O) (CCA_dec_ll A));auto => /=.
      by rewrite FDistr.dt_ll  DBool.dbool_ll dk_ll.
    have : Pr[DDH1_ex(B_DDH(A)).main() @ &m : res] <= 
           Pr[Ad1.Main(G1).main() @ &m : res \/ G1.bad].
    + byequiv DDH1_G1 => //;1: smt ().
    (* print glob G1. *)
    have /= := Ad1.pr_abs G1 _ _ &m (fun (b:bool) (x : glob G1) => b \/ x.`14).
    + proc;auto => />; by rewrite dt_r_ll ?FDistr.dt_ll.
    + proc;auto;call (guess_ll (<:G1.O) G1_dec_ll);auto.
      by call (choose_ll (<:G1.O) G1_dec_ll);auto; rewrite dk_ll  FDistr.dt_ll DBool.dbool_ll.  
    smt (mu_bounded).
  qed.

  local module G2 = {

    module O = G1.O

    module A = G1.A

    var alpha, v: t

    proc main1 () = {
      var m0, m1, b, b0, v, e, f, h, r', a, a_, c, d;
      G1.log <- [];
      G1.cstar <- None;
      G1.bad <- false;
      G1.w <$ FDistr.dt \ (pred1 F.zero);
      G1.u <$ FDistr.dt; 
      G1.u' <$ FDistr.dt \ (pred1 G1.u);
      G1.g_ <- g ^ G1.w; G1.k  <$ dk;
      a <- g^G1.u; a_ <- G1.g_^G1.u';
      G1.x <$ FDistr.dt; G1.x2 <$ FDistr.dt; G1.x1 <- G1.x - G1.w * G1.x2; e <- g^G1.x;
      G1.y <$ FDistr.dt; G1.y2 <$ FDistr.dt; G1.y1 <- G1.y - G1.w * G1.y2; f <- g^G1.y;
      G1.z <$ FDistr.dt; h <- g^G1.z; 
      (m0,m1) <@ A.choose(G1.k, g, G1.g_, e, f, h); 
      b <$ {0,1}; 
      r' <$ FDistr.dt; 
      c <- g^r';
      v <- H G1.k (a, a_, c);
      d <- a^(G1.x1 + v*G1.y1) * a_^(G1.x2+v*G1.y2);
      G1.cstar <- Some (a,a_,c,d);
      b0 <@ A.guess(a,a_,c,d);
      return (b = b0);
    }
  
    proc main () = {
      var m0, m1, b, b0, e, f, h, r, r', a, a_, c, d;
      G1.log <- [];
      G1.cstar <- None;
      G1.bad <- false;
      G1.w <$ FDistr.dt \ (pred1 F.zero);
      G1.u <$ FDistr.dt; 
      G1.u' <$ FDistr.dt \ (pred1 G1.u);
      G1.g_ <- g ^ G1.w; G1.k  <$ dk;
      a <- g^G1.u; a_ <- G1.g_^G1.u';
      G1.y <$ FDistr.dt; G1.y2 <$ FDistr.dt; G1.y1 <- G1.y - G1.w * G1.y2; f <- g^G1.y;
      G1.z <$ FDistr.dt; r' <$ FDistr.dt; h <- g^G1.z;
      c <- g^r';
      v <- H G1.k (a, a_, c);
      G1.x <$ FDistr.dt; r <$ FDistr.dt;
      alpha <- (r - G1.u*(G1.x + v*G1.y))/ (G1.w*(G1.u'-G1.u));
      G1.x2 <- alpha - v*G1.y2;
      G1.x1 <- G1.x - G1.w * G1.x2; e <- g^G1.x;
      d <- g ^ r;
      (m0,m1) <@ A.choose(G1.k, g, G1.g_, e, f, h); 
      G1.cstar <- Some (a,a_,c,d);
      b0 <@ A.guess(a,a_,c,d);
      b <$ {0,1}; 
      return (b = b0);
    }
  }.

  local equiv G1_G21 : Ad1.MainE(G1).main ~ G2.main1 : ={glob A} ==> ={res, G1.bad}.
  proof.
    proc;inline *;wp.
    call (_: ={G1.bad, G1.cstar, G1.log, G1.x, G1.x1, G1.x2, G1.y, 
               G1.y1, G1.y2, G1.z, G1.w, G1.k}).
    + by sim => />.
    swap{1} [23..24] 3;wp => /=.
    rnd  (fun z2 => G1.u*G1.z - G1.u*G1.w*z2 + G1.w*G1.u'* z2 + log (b ? m1 : m0)){1}
         (fun r' => (r' - G1.u*G1.z - log (b ? m1 : m0)) / (G1.w * (G1.u' - G1.u))){1}.
    rnd.
    call (_: ={G1.bad, G1.cstar, G1.log, G1.x, G1.x1, G1.x2, G1.y,
               G1.y1, G1.y2, G1.z, G1.w, G1.k}).
    + by sim => />.
    auto => &m1 &m2 />;rewrite /pred1 -ofint0.
    move=> wL /supp_dexcepted [] _ /= HwL uL _ u'L /supp_dexcepted [] _ /= Hu'L .
    move=> kL _ xL _ x2L _ yL _ y2L _ zL _ resu bL _.
    have H1 : (-uL) * wL + u'L * wL = wL * (u'L - uL) by ring.
    have H2 : (-uL) * wL + u'L * wL <> F.ofint 0.
    + rewrite H1 ofint0 mulf_eq0 negb_or -{1}ofint0 HwL /=.
      by move: Hu'L;apply: contra => H;ring H.
    split => [? _ | _ ]; 1: by field.
    move=> z2L _; split => [ | _]; 1: by field.
    pose HH1 := H _ _; pose HH2 := H _ _.    
    have -> : HH1 = HH2.
    + rewrite /HH1 /HH2;do 2!congr.
      by rewrite log_bij !(log_g, log_pow, log_mul);ring.
    progress; rewrite log_bij !(log_g, log_pow, log_mul);field => //.
  qed.

  local equiv G21_G2 : G2.main1 ~ G2.main : ={glob A} ==> ={res, G1.bad}.
  proof.
    proc;inline *;wp. swap{2} -2.
    call (_: ={G1.bad, G1.cstar, G1.log, G1.x, G1.x1, G1.x2, G1.y, 
               G1.y1, G1.y2, G1.z, G1.w, G1.k}).
    + by sim => />.
    wp;swap {1} [11..14] 6;swap{1} -7;rnd.
    call (_: ={G1.bad, G1.cstar, G1.log, G1.x, G1.x1, G1.x2, G1.y, 
               G1.y1, G1.y2, G1.z, G1.w, G1.k}).
    + by sim => />.
    wp.
    rnd (fun x2 => (x2 + G2.v*G1.y2) * (G1.w*(G1.u'-G1.u)) + G1.u*(G1.x + G2.v*G1.y)){2}
        (fun r => (r - G1.u*(G1.x + G2.v*G1.y))/ (G1.w*(G1.u'-G1.u)) - G2.v*G1.y2){2}.
    auto => &m1 &m2 />;rewrite /pred1 -ofint0.
    move=> wL /supp_dexcepted [] _ /= HwL uL _ u'L /supp_dexcepted [] _ /= Hu'L .
    move=> kL _ yL _ y2L _ zL _ r'L _ xL _.  
    have H1 : (-uL) * wL + u'L * wL = wL * (u'L - uL) by ring.
    have H2 : (-uL) * wL + u'L * wL <> F.ofint 0.
    + rewrite H1 ofint0 mulf_eq0 negb_or -{1}ofint0 HwL /=.
      by move: Hu'L;apply: contra => H;ring H.
    split => [? _ | _ ]; 1: by field.
    move=> z2L _; split => [ | _]; 1: by field.
    by progress;2..3:rewrite log_bij !(log_g, log_pow, log_mul);field.
  qed.

  local lemma pr_G2_res &m: Pr[G2.main() @ &m : res] <= 1%r/2%r.
  proof.
    byphoare=> //;proc;rnd;conseq (_: _ ==> true) => //=.
    by move=> ?;rewrite DBool.dbool1E.
  qed.

  local module G3 = {
    var g3 : ( group * group * group) option
    var y2log : t list
    var cilog : ciphertext list
    var a, a_, c, d: group

    module O = {
      proc dec(ci:ciphertext) = {
        var m, a,a_,c,d,v, y2';
        m <- None;
        if (size G1.log < PKE_.qD && Some ci <> G1.cstar) {
          cilog <- (G1.cstar = None) ? ci :: cilog : cilog;
          G1.log <- ci :: G1.log;
          (a,a_,c,d) <- ci;
          v <- H G1.k (a, a_, c);
          if (a_ <> a^G1.w) {
            if (v = G2.v /\ (a,a_,c) <> (G3.a,G3.a_,G3.c)) g3 <- Some (a,a_,c);
            else {
              y2' <- ((log d - log a*(G1.x + v*G1.y))/(log a_ - log a*G1.w) - G2.alpha) / (v -G2.v);
              y2log <-  y2' :: y2log;
            }
          }
          m <- if (a_ = a^G1.w /\ d = a ^ (G1.x + v*G1.y)) then Some (c / a ^ G1.z)
              else None;
        }
        return m;
      }
    }

    module A = A (O)

    proc main () = {
      var m0, m1, b0, e, f, h, r, r';
      G1.log <- [];
      G3.y2log <- [];
      G3.cilog <- [];
      G3.g3 <- None;
      G1.cstar <- None;
      G1.w <$ FDistr.dt \ (pred1 F.zero);
      G1.u <$ FDistr.dt; 
      G1.u' <$ FDistr.dt \ (pred1 G1.u);
      G1.g_ <- g ^ G1.w; G1.k  <$ dk;
      a <- g^G1.u; a_ <- G1.g_^G1.u';
      G1.y <$ FDistr.dt; f <- g^G1.y;
      G1.z <$ FDistr.dt; r' <$ FDistr.dt; h <- g^G1.z;
      c <- g^r';
      G2.v <- H G1.k (a, a_, c);
      G1.x <$ FDistr.dt; r <$ FDistr.dt; e <- g^G1.x;
      G2.alpha <- (r - G1.u*(G1.x + G2.v*G1.y))/ (G1.w*(G1.u'-G1.u));     
      d <- g ^ r;
      (m0,m1) <@ A.choose(G1.k, g, G1.g_, e, f, h); 
      G1.cstar <- Some (a,a_,c,d);
      b0 <@ A.guess(a,a_,c,d);
      G1.y2 <$ FDistr.dt; 
      G1.y1 <- G1.y - G1.w * G1.y2;
      G1.x2 <- G2.alpha - G2.v*G1.y2;
      G1.x1 <- G1.x - G1.w * G1.x2; 
    }
  }.

  local equiv G2_G3_dec :  G1.O.dec ~ G3.O.dec : 
    ! (G3.g3 <> None \/ (G3.a, G3.a_,G3.c, G3.d) \in G3.cilog){2}  /\
    ={ci} /\ ={G1.x, G1.y, G1.z, G1.x1, G1.x2, G1.y1, G1.y2, G1.log, G1.cstar, G1.w,
               G1.u, G1.u', G1.k} /\
    (G1.cstar <> None => G1.cstar = Some (G3.a,G3.a_,G3.c,G3.d)){2} /\
    (G3.d = G3.a^(G1.x1 + G2.v*G1.y1) * G3.a_^(G1.x2+G2.v*G1.y2) /\
     G1.y1 = G1.y - G1.w * G1.y2 /\
     G1.x1 = G1.x - G1.w * G1.x2 /\
     G1.x2 = G2.alpha - G2.v * G1.y2){2} /\
    (G1.bad{1} => G1.y2{2} \in G3.y2log{2}) ==>
    !(G3.g3 <> None \/ (G3.a, G3.a_,G3.c, G3.d) \in G3.cilog){2} =>
     (={res} /\ ={G1.x, G1.y, G1.z, G1.x1, G1.x2, G1.y1, G1.y2, G1.log, G1.cstar, G1.w,
                 G1.u, G1.u', G1.k} /\
      (G1.cstar <> None => G1.cstar = Some (G3.a,G3.a_,G3.c,G3.d)){2} /\
      (G3.d = G3.a^(G1.x1 + G2.v*G1.y1) * G3.a_^(G1.x2+G2.v*G1.y2) /\
       G1.y1 = G1.y - G1.w * G1.y2 /\
       G1.x1 = G1.x - G1.w * G1.x2 /\
       G1.x2 = G2.alpha - G2.v * G1.y2){2} /\
      (G1.bad{1} => G1.y2{2} \in G3.y2log{2})).
  proof.
    proc;auto => &m1 &m2 />.
    case: (ci{m2}) => a a_ c d /=.
    pose v := H _ _. rewrite !negb_or => [[]] Hg3 Hcilog Hstareq.
    rewrite Hg3 /=. 
    case: (G1.bad{m1}) => [_ -> | ] //=. 
    move=> Hbad Hsize Hstar;rewrite !negb_and /= 2!negb_or /= -!andaE.
    case (v = G2.v{m2}) => [->> /= ? [#]!->> Hstar1 ->>| /=].
    + by case: (G1.cstar{m2}) Hstareq Hstar Hstar1.
    move=> Hv Ha _ ->>;left.
    rewrite !(log_g, log_pow, log_mul);field => //.
    + by move: Hv;apply: contra;rewrite ofint0 => H;ring H.
    by move: Ha;apply: contra; rewrite log_bij log_pow ofint0 => H;ring H.
  qed.

  local equiv G2_G3 : G2.main ~ G3.main : 
    ={glob A} ==> 
      !(G3.g3 <> None \/ (G3.a, G3.a_,G3.c, G3.d) \in G3.cilog){2} => 
      (G1.bad{1} => (G1.y2 \in G3.y2log){2}).
  proof.
    proc.
    swap{2} [28..29] -14. swap{2} [30..31] -4. rnd{1}.
    call (_ : (G3.g3 <> None \/ (G3.a, G3.a_,G3.c, G3.d) \in G3.cilog),
               (={G1.x, G1.y, G1.z, G1.x1, G1.x2, G1.y1, G1.y2, G1.log, G1.cstar, G1.w,
                  G1.u, G1.u', G1.k} /\
                (G1.cstar <> None => G1.cstar = Some (G3.a,G3.a_,G3.c,G3.d)){2} /\
                (G3.d = G3.a^(G1.x1 + G2.v*G1.y1) * G3.a_^(G1.x2+G2.v*G1.y2) /\
                 G1.y1 = G1.y - G1.w * G1.y2 /\
                 G1.x1 = G1.x - G1.w * G1.x2 /\
                 G1.x2 = G2.alpha - G2.v * G1.y2){2} /\
                (G1.bad{1} => G1.y2{2} \in G3.y2log{2}))).
    + by apply guess_ll.
    + by apply G2_G3_dec.
    + by move=> &m2 _;apply G1_dec_ll.
    + by move=> /=;proc;auto => /#.
    wp;call (_ : (G3.g3 <> None \/ (G3.a, G3.a_,G3.c, G3.d) \in G3.cilog),
               (={G1.x, G1.y, G1.z, G1.x1, G1.x2, G1.y1, G1.y2, G1.log, G1.cstar, G1.w,
                  G1.u, G1.u', G1.k} /\
                (G1.cstar <> None => G1.cstar = Some (G3.a,G3.a_,G3.c,G3.d)){2} /\
                (G3.d = G3.a^(G1.x1 + G2.v*G1.y1) * G3.a_^(G1.x2+G2.v*G1.y2) /\
                 G1.y1 = G1.y - G1.w * G1.y2 /\
                 G1.x1 = G1.x - G1.w * G1.x2 /\
                 G1.x2 = G2.alpha - G2.v * G1.y2){2} /\
                (G1.bad{1} => G1.y2{2} \in G3.y2log{2}))).
    + by apply choose_ll. 
    + by apply G2_G3_dec.
    + by move=> &m2 _;apply G1_dec_ll.
    + by move=> /=;proc;auto => /#.
    auto => &m1 &m2 />.
    move=> wL /supp_dexcepted [] _;rewrite /pred1 -F.ofint0 => HwL0.
    move=> uL _ u'L /supp_dexcepted [] _ /= HuL kL _.
    move=> yL _ y2L _ zL _ r'L _ xL _ rL _.
    have H1 : (-uL) * wL + u'L * wL = wL * (u'L - uL) by ring.
    have H2 : (-uL) * wL + u'L * wL <> F.ofint 0.
    + rewrite H1 ofint0 mulf_eq0 negb_or -{1}ofint0 HwL0 /=.
      by move: HuL;apply: contra => H;ring H.
    split => [ | _].
    + by rewrite log_bij !(log_g, log_pow, log_mul);field.
    smt(). 
  qed.

  local lemma pr_G3_y2log &m : 
    Pr[G3.main() @ &m : G1.y2 \in G3.y2log] <= PKE_.qD%r / q%r.
  proof. 
    byphoare => //;proc;wp;rnd.
    conseq (_: _ ==> size G3.y2log <=  PKE_.qD) => /=.
    + move=> y2log Hsize;apply (ler_trans ((size y2log)%r/q%r)).
      + by apply (mu_mem_le_mu1 FDistr.dt y2log (inv q%r)) => x;rewrite FDistr.dt1E.
      apply ler_wpmul2r => //;2: by apply le_fromint.
      apply invr_ge0;smt (le_fromint gt1_q).
    call (_: size G3.y2log <= size G1.log /\ size G3.y2log <= PKE_.qD). 
    + proc;auto => /#. 
    auto;call (_: size G3.y2log <= size G1.log /\ size G3.y2log <= PKE_.qD). 
    + proc;auto => /#. 
    auto => />;smt (qD_pos).
  qed.

  local equiv G3_TCR : G3.main ~ TCR(B_TCR(A)).main : ={glob A} ==> G3.g3{1} <> None => res{2}.
  proof.
    proc;inline *;wp;rnd{1}.
    call (_ : B_TCR.log{2} = G1.log{1} /\
              B_TCR.cstar{2} = G1.cstar{1} /\
              B_TCR.k{2} = G1.k{1} /\ 
              B_TCR.x{2} = G1.x{1} /\ B_TCR.y{2} = G1.y{1} /\ B_TCR.z{2} = G1.z{1} /\
              B_TCR.a{2} = G3.a{1} /\ B_TCR.a_{2} = G3.a_{1} /\ B_TCR.c{2} = G3.c{1} /\
              B_TCR.v'{2} = G2.v{1} /\
              B_TCR.w{2}  = G1.w{1} /\
              B_TCR.g3{2} = G3.g3{1} /\
              (G3.g3{1} <> None => 
               (H B_TCR.k (oget B_TCR.g3) = B_TCR.v' /\ (oget B_TCR.g3) <> 
                                                   (B_TCR.a,B_TCR.a_,B_TCR.c)){2})).
    + by proc;auto=> /#.
    wp; call (_ : B_TCR.log{2} = G1.log{1} /\
              B_TCR.cstar{2} = G1.cstar{1} /\
              B_TCR.k{2} = G1.k{1} /\ 
              B_TCR.x{2} = G1.x{1} /\ B_TCR.y{2} = G1.y{1} /\ B_TCR.z{2} = G1.z{1} /\
              B_TCR.a{2} = G3.a{1} /\ B_TCR.a_{2} = G3.a_{1} /\ B_TCR.c{2} = G3.c{1} /\
              B_TCR.v'{2} = G2.v{1} /\
              B_TCR.w{2}  = G1.w{1} /\
              B_TCR.g3{2} = G3.g3{1} /\
              (G3.g3{1} <> None => 
               (H B_TCR.k (oget B_TCR.g3) = B_TCR.v' /\ (oget B_TCR.g3) <> 
                                                   (B_TCR.a,B_TCR.a_,B_TCR.c)){2})).
    + by proc;auto=> /#.
    swap{1} 16 -7;auto; smt (FDistr.dt_ll).
  qed.


 local module G4 = {

    module O = {
      proc dec(ci:ciphertext) = {
        var m, a,a_,c,d,v;
        m <- None;
        if (size G1.log < PKE_.qD && Some ci <> G1.cstar) {
          G3.cilog <- (G1.cstar = None) ? ci :: G3.cilog : G3.cilog;
          G1.log <- ci :: G1.log;
          (a,a_,c,d) <- ci;
          v <- H G1.k (a, a_, c);
          m <- if (a_ = a^G1.w /\ d = a ^ (G1.x + v*G1.y)) then Some (c / a ^ G1.z)
              else None;
        }
        return m;
      }
    }

    module A = A (O)

    proc main () = {
      var m0, m1, b0, e, f, h, r, r';
      G1.log <- [];
      G3.cilog <- [];
      G1.cstar <- None;
      G1.w <$ FDistr.dt \ (pred1 F.zero);
      G1.g_ <- g ^ G1.w;
     
      G1.k  <$ dk;
      G1.y <$ FDistr.dt; f <- g^G1.y;
      G1.z <$ FDistr.dt;  h <- g^G1.z; 
      G1.x <$ FDistr.dt; e <- g^G1.x;
      (m0,m1) <@ A.choose(G1.k, g, G1.g_, e, f, h);
      G1.u <$ FDistr.dt; 
      G1.u' <$ FDistr.dt \ (pred1 G1.u); 
      r' <$ FDistr.dt; 
      r <$ FDistr.dt;
      G3.a <- g^G1.u; G3.a_ <- G1.g_^G1.u';G3.c <- g^r'; G3.d <- g ^ r;
      G2.v <- H G1.k (G3.a, G3.a_, G3.c);
      G2.alpha <- (r - G1.u*(G1.x + G2.v*G1.y))/ (G1.w*(G1.u'-G1.u));      
      G1.cstar <- Some (G3.a,G3.a_,G3.c,G3.d);
      b0 <@ A.guess(G3.a,G3.a_,G3.c,G3.d);
    }
  }.

  local equiv G3_G4 : G3.main ~ G4.main : ={glob A} ==> ={G3.a, G3.a_,G3.c, G3.d, G3.cilog}.
  proof.
    proc;wp;rnd{1}.
    call (_ : ={G1.log, G1.cstar, G1.k, G1.w, G1.x, G1.y, G1.z, G3.cilog}).
    + by proc;auto => />.
    wp. swap{2} [14..17] -1.
    call (_ : ={G1.log, G1.cstar, G1.k, G1.w, G1.x, G1.y, G1.z, G3.cilog}).
    + by proc;auto => />.
    swap{2} [13..14]-8.  swap{2} [13..14]1.
    by auto => />;rewrite FDistr.dt_ll.
  qed.

  (* TODO: move this ?*)
  lemma mu_mem_le_mu1_size (dt : 'a distr) (l : 'a list) (r : real) n: 
    size l <= n => 
    (forall (x : 'a), mu1 dt x <= r) => mu dt (mem l) <= n%r * r.
  proof.
    move=> Hsize Hmu1;apply (ler_trans ((size l)%r * r)). 
    + by apply mu_mem_le_mu1.
    apply ler_wpmul2r; 1: smt (mu_bounded). 
    by apply le_fromint.
  qed.

  local lemma pr_G4 &m:
    Pr[G4.main() @ &m : (G3.a, G3.a_,G3.c, G3.d) \in G3.cilog] <=
      (PKE_.qD%r/q%r)^3 * (PKE_.qD%r/(q-1)%r).
  proof.
    byphoare=> //;proc.
    seq 23 : ((G3.a, G3.a_, G3.c, G3.d) \in G3.cilog) 
             ((PKE_.qD%r / q%r)^3 * (PKE_.qD%r / (q - 1)%r)) 1%r _ 0%r => //;last first.
    + hoare; call (_ : G1.cstar <> None /\ !(G3.a, G3.a_, G3.c, G3.d) \in G3.cilog).
      + by proc;auto => /#.
      by auto.      
    seq 13 : true 1%r ((PKE_.qD%r / q%r) ^ 3 * (PKE_.qD%r / (q - 1)%r))
                 0%r _ (size G3.cilog <= PKE_.qD /\ G1.w <> F.zero /\ G1.g_ = g ^ G1.w) => //.
    + call (_ : size G3.cilog <= size G1.log /\ size G1.log <= PKE_.qD).
      + proc;auto => /#.
      auto => /= w /supp_dexcepted;smt (qD_pos).
    wp;conseq (_ : _ ==> G1.u \in map (fun (g4:ciphertext) => log g4.`1) G3.cilog /\
                      G1.u' \in map (fun (g4:ciphertext) => log g4.`2 / G1.w) G3.cilog /\
                      r' \in map (fun (g4:ciphertext) => log g4.`3) G3.cilog /\
                      r \in map (fun (g4:ciphertext) => log g4.`4) G3.cilog).
    + move=> &hr />;rewrite -ofint0 => _ Hw u u' r r' Hlog.
      do !split;apply mapP;
       exists (G.g ^ u, g ^ G1.w{hr} ^ u', G.g ^ r', G.g ^ r);
       rewrite Hlog /= !log_pow ?log_g;1,3,4: by ring. 
       by field.
    seq 1 : (G1.u \in map (fun (g4 : ciphertext) => log g4.`1) G3.cilog)
            (PKE_.qD%r / q%r) ((PKE_.qD%r / q%r)^2 * (PKE_.qD%r / (q - 1)%r))
            _ 0%r (size G3.cilog <= PKE_.qD) => //;
    last 2 first.
    + hoare;conseq (_ : _ ==> true) => // /#.
    + move=> &hr _;apply lerr_eq;ring.
    + by auto.
    + rnd;skip => /> &hr Hsize _;pose m' := map _ _.
      apply (mu_mem_le_mu1_size FDistr.dt m') => //.
      + by rewrite /m' size_map.
      by move=> ?;rewrite FDistr.dt1E.
    seq 1 : (G1.u' \in map (fun (g4 : ciphertext) => log g4.`2 / G1.w) G3.cilog)
            (PKE_.qD%r / (q-1)%r) ((PKE_.qD%r / q%r)^2) _ 0%r 
            (size G3.cilog <= PKE_.qD) => //;last 2 first.
    + hoare;conseq (_ : _ ==> true) => // /#.
    + move=> &hr _;apply lerr_eq;ring.
    + by auto.
    + rnd;skip => /> &hr Hsize _;pose m' := map _ _.
      apply (mu_mem_le_mu1_size (FDistr.dt \ pred1 G1.u{hr}) m') => //.
      + by rewrite /m' size_map.
      move=> x;rewrite dexcepted1E {1}/pred1. 
      case: (x = G1.u{hr}) => _.
      + apply invr_ge0;smt (le_fromint gt1_q).
      rewrite FDistr.dt_ll !FDistr.dt1E;apply lerr_eq.
      field;smt (gt1_q le_fromint). 
    seq 1 : (r' \in map (fun (g4 : ciphertext) => log g4.`3) G3.cilog)
            (PKE_.qD%r / q%r) (PKE_.qD%r / q%r) _ 0%r 
            (size G3.cilog <= PKE_.qD) => //;last 2 first.
    + hoare;conseq (_ : _ ==> true) => // /#.
    + move=> &hr _;apply lerr_eq;field.
      + rewrite expr2; smt (gt1_q). 
      + smt (gt1_q). 
    + by auto.
    + rnd;skip => /> &hr Hsize _;pose m' := map _ _.
      apply (mu_mem_le_mu1_size FDistr.dt m') => //.
      + by rewrite /m' size_map.
      by move=> ?;rewrite FDistr.dt1E.
    conseq (_ : _ ==> (r \in map (fun (g4 : ciphertext) => log g4.`4) G3.cilog)) => //.
    rnd;skip => /> &hr Hsize _;pose m' := map _ _.
    apply (mu_mem_le_mu1_size FDistr.dt m') => //.
    + by rewrite /m' size_map.
    by move=> ?;rewrite FDistr.dt1E.
  qed.

  lemma aux2 &m : 
    Pr[CCA(CramerShoup, A).main() @ &m : res] <=
    `|Pr[DDH0(B_DDH(A)).main() @ &m : res] -
      Pr[DDH1(B_DDH(A)).main() @ &m : res]| +
    Pr[TCR(B_TCR(A)).main() @ &m : res] + 
    1%r/2%r + (PKE_.qD + 3)%r / q%r + (PKE_.qD%r/q%r)^3 * (PKE_.qD%r/(q-1)%r).
  proof.
    have := aux1 &m.
    have -> : Pr[Ad1.MainE(G1).main() @ &m : res \/ G1.bad] = 
              Pr[G2.main1() @ &m : res \/ G1.bad].
    + by byequiv G1_G21.
    have -> : Pr[G2.main1() @ &m : res \/ G1.bad] = Pr[G2.main() @ &m : res \/ G1.bad].
    + by byequiv G21_G2.
    have : Pr[G2.main() @ &m : res \/ G1.bad] <= 1%r/2%r + Pr[G2.main() @ &m : G1.bad].
    + by rewrite Pr [mu_or];have := (pr_G2_res &m);smt (mu_bounded).
    have : Pr[G2.main() @ &m : G1.bad] <= 
           Pr[G3.main() @ &m : G3.g3 <> None \/ (G3.a, G3.a_,G3.c, G3.d) \in G3.cilog \/
                               G1.y2 \in G3.y2log].
    + byequiv G2_G3 => // /#.                                
    rewrite Pr [mu_or];rewrite Pr [mu_or].
    have : Pr[G3.main() @ &m : G3.g3 <> None] <= Pr[TCR(B_TCR(A)).main() @ &m : res].
    + byequiv G3_TCR => //.
    have : Pr[G3.main() @ &m : (G3.a, G3.a_,G3.c, G3.d) \in G3.cilog] =
           Pr[G4.main() @ &m : (G3.a, G3.a_,G3.c, G3.d) \in G3.cilog].
    + byequiv G3_G4=> //.
    have := pr_G4 &m.
    have := pr_G3_y2log &m.
    have -> : (PKE_.qD + 3)%r / q%r = PKE_.qD%r/q%r + 3%r/q%r.
    + by rewrite fromintD;ring.
    smt (mu_bounded).
  qed.

end section Security_Aux.

section Security.

  declare module A : CCA_ADV {CCA, B_TCR}.
  axiom guess_ll : forall (O <: CCA_ORC{A}), islossless O.dec => islossless A(O).guess.
  axiom choose_ll : forall (O <: CCA_ORC{A}), islossless O.dec => islossless A(O).choose.

  local module NA (O:CCA_ORC) = {
    module A = A(O)
    proc choose = A.choose
    proc guess(c:ciphertext) = {
      var b;
      b <@ A.guess(c);
      return !b;
    }
  }.

  local lemma CCA_NA &m : 
     Pr[CCA(CramerShoup, A).main() @ &m : res] = 
     1%r - Pr[CCA(CramerShoup, NA).main() @ &m : res].
  proof.
    have -> : Pr[CCA(CramerShoup, NA).main() @ &m : res] = 
              Pr[CCA(CramerShoup, A).main() @ &m : !res].
    + byequiv=> //;proc;inline *;wp.
      by conseq (_ : _ ==> ={b} /\ b'{2} = b0{1});[ smt() | sim].
    rewrite Pr [mu_not].
    have -> : Pr[CCA(CramerShoup, A).main() @ &m : true] = 1%r;last by ring.
    byphoare=> //;proc; islossless.
    + by apply (guess_ll (<:CCA(CramerShoup, A).O) (CCA_dec_ll A)).
    + by apply (choose_ll (<:CCA(CramerShoup, A).O) (CCA_dec_ll A)).
    apply dexcepted_ll; 1: by apply FDistr.dt_ll.
    rewrite FDistr.dt1E;smt (le_fromint gt1_q).  
  qed.

  local lemma DDH0_NA &m : Pr[DDH0(B_DDH(NA)).main() @ &m : res] = 
                        1%r - Pr[DDH0(B_DDH(A)).main() @ &m : res].
  proof.
    have -> : Pr[DDH0(B_DDH(NA)).main() @ &m : res] = 
              Pr[DDH0(B_DDH(A)).main() @ &m : !res].
    + byequiv=> //;proc;inline *;wp.
      by conseq (_ : _ ==> ={b0} /\ b'{2} = b1{1});[ smt() | sim].   
    rewrite Pr [mu_not];congr.
    byphoare=> //;proc;inline *;auto.
    islossless.
    + by apply (guess_ll (<:CCA(CramerShoup, A).O) (CCA_dec_ll A)).
    by apply (choose_ll (<:CCA(CramerShoup, A).O) (CCA_dec_ll A)).
  qed.

  local lemma DDH1_NA &m : Pr[DDH1(B_DDH(NA)).main() @ &m : res] = 
                        1%r - Pr[DDH1(B_DDH(A)).main() @ &m : res].
  proof.
    have -> : Pr[DDH1(B_DDH(NA)).main() @ &m : res] = 
              Pr[DDH1(B_DDH(A)).main() @ &m : !res].
    + byequiv=> //;proc;inline *;wp.
      by conseq (_ : _ ==> ={b0} /\ b'{2} = b1{1});[ smt() | sim].   
    rewrite Pr [mu_not];congr.
    byphoare=> //; islossless.
    + by apply (guess_ll (<:CCA(CramerShoup, A).O) (CCA_dec_ll A)).
    by apply (choose_ll (<:CCA(CramerShoup, A).O) (CCA_dec_ll A)).
  qed.

  local lemma TCR_NA &m : Pr[TCR(B_TCR(NA)).main() @ &m : res] = 
                          Pr[TCR(B_TCR(A)).main() @ &m : res].
  proof.
    byequiv=> //;proc;inline *;sim.
    call (_: ={ B_TCR.v', B_TCR.k, B_TCR.cstar, B_TCR.a, B_TCR.a_, B_TCR.c,
                B_TCR.log, B_TCR.g3, B_TCR.w, B_TCR.x, B_TCR.y, B_TCR.z}).
    + by sim.
    auto;call (_: ={ B_TCR.v', B_TCR.k, B_TCR.cstar, B_TCR.a, B_TCR.a_, B_TCR.c,
                     B_TCR.log, B_TCR.g3, B_TCR.w, B_TCR.x, B_TCR.y, B_TCR.z});2: by auto.
    by sim.
  qed.

  lemma conclusion &m : 
    `|Pr[CCA(CramerShoup, A).main() @ &m : res] - 1%r/2%r | <=
    `|Pr[DDH0(B_DDH(A)).main() @ &m : res] - Pr[DDH1(B_DDH(A)).main() @ &m : res]| +
    Pr[TCR(B_TCR(A)).main() @ &m : res] + 
    (PKE_.qD + 3)%r / q%r + (PKE_.qD%r/q%r)^3 * (PKE_.qD%r/(q-1)%r).
  proof.
    case (Pr[CCA(CramerShoup, A).main() @ &m : res] <= 1%r/2%r);last first.
    + have /# := aux2 A guess_ll choose_ll &m.
    have := aux2 NA _ choose_ll &m.            
    + by move=> O O_ll;proc;inline *;call (_ : true) => //; apply guess_ll.
    rewrite (CCA_NA &m) (DDH0_NA &m) (DDH1_NA &m) (TCR_NA &m).
    smt (mu_bounded).
  qed.

end section Security.

