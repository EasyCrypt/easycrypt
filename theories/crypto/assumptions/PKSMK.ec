require import AllCore Distr DInterval FSet List SmtMap.
require PROM PlugAndPray.

(***************************************)
(* Definitions for Public-Key Signatures 
   Schemes in a multi-key setting      *)
(***************************************)

type pkey.
type skey.
type message.
type signature.

type keys = pkey * skey.

(* Signature are defined by the 3 following operators *)
op keygen : keys distr.
op sign   : skey * message -> signature distr.
op verify : pkey * message * signature -> bool.

axiom keygen_ll : is_lossless keygen.
axiom sign_ll s m : is_lossless (sign (s,m)).

hint exact random : keygen_ll sign_ll.

axiom verify_sign : forall pk sk m s, 
  (pk,sk) \in keygen =>
  s \in sign (sk,m) => verify (pk, m, s).

module type SigService = {
  proc init () : unit
  proc keygen () : pkey
  proc sign (pk:pkey, m:message) : signature option
  proc pkeys () : pkey fset
}.

module type SigServiceV = {
  proc verify(pk:pkey, m:message, s:signature): bool
}.

module type FullSigService = {
  include SigService
  include SigServiceV
}.

op q_gen : { int | 0 < q_gen } as lt0_q_gen.
op q_sig : int.

module RealSigServ : FullSigService = {
  var pks_sks : (pkey, skey) fmap
  var qs : (pkey * message * signature) fset
  var count_pk : int
  var count_sig : int

  proc init () = { 
      pks_sks <- empty; 
      qs <- fset0;
      count_pk <- 0;
      count_sig <- 0;
  }

  proc keygen () = {
    var pk,sk;
    pk <- witness;
    if (count_pk < q_gen) {
       (pk,sk) <$ keygen;
       if (pk \notin pks_sks) { pks_sks.[pk] <- sk; }
       count_pk <- count_pk + 1;
    }
    return pk;
  }

  proc sign(pk:pkey, m:message): signature option = {
    var s,r;
    r <- None;
    if (count_sig < q_sig) {
       if (pk \in pks_sks) {
         s <$ sign(oget pks_sks.[pk], m);
         r <- Some s;
         qs <- qs `|` fset1 (pk, m, s);
       }
       count_sig <- count_sig + 1;
    }
    return r;
  }
 
  proc pkeys () = { return fdom pks_sks; }

  proc verify (pk:pkey, m:message, s:signature) = {
    return verify(pk, m, s);
  }
}.

module IdealSigServ : FullSigService = {
  
  include RealSigServ [-verify]
  proc verify (pk:pkey, m:message, s:signature) = {
    return if (pk \in RealSigServ.pks_sks)
           then (pk, m, s) \in RealSigServ.qs
           else verify(pk, m, s);
  }

}.

(* Definition of unforgeability *)

module type OrclUF = {
  include SigService [-init] 
  proc forge(pk:pkey, m:message, s:signature): unit
}.

module type AdvUF (O:OrclUF) = {
  proc main() : unit
}.

op is_forgery pk m s (pks_sks : (pkey, skey) fmap) 
              ( qs : (pkey * message * signature) fset) = 
  pk \in pks_sks /\ (verify (pk, m, s) /\ !(pk,m,s) \in qs).

module OrclUF : OrclUF = {

  var forged : bool

  proc init() = { forged <- false; RealSigServ.init(); }

  include RealSigServ [keygen,sign,pkeys]

  proc forge (pk:pkey, m:message, s:signature) = {
    forged <- forged || is_forgery pk m s RealSigServ.pks_sks RealSigServ.qs;
  }
}.

module UF (A:AdvUF) = {

  proc main () = {
    OrclUF.init();
    A(OrclUF).main();
    return OrclUF.forged;
  }

}.

(* ----------------------------------------------------------------------------- *)
(* We prove that for all adversaries which is able to distinguish between        *)
(* RealSigServ and IdealSigServ there exists a adversary which is able to win    *)
(* the unforgeability game.                                                      *)
(* ----------------------------------------------------------------------------- *)

module type OrclInd = {
  include FullSigService [-init]
}.

module type AdvInd(O:OrclInd) = {
  proc main () : bool
}.

module IndSig (O:FullSigService, A:AdvInd) = {
  proc main() : bool = {
    var b;
    O.init();
    b <@ A(O).main();
    return b;
  }
}.

module (MkAdvUF(A:AdvInd):AdvUF) (O:OrclUF) = {
    module OA = {
      include O [-forge] 
      proc verify(pk : pkey, m : message, s : signature) : bool = {
        O.forge(pk, m, s);
        return  verify(pk, m, s);
      }
    }
    
    proc main () = {
      var b;
      b <@ A(OA).main();
    }
  }.

section.

  declare module A:AdvInd { RealSigServ, OrclUF }.

  local module Wrap (O:FullSigService) = {
    include OrclUF [+init]
    include O [- init, verify]
    proc verify(pk : pkey, m : message, s : signature) : bool = {
      var b;
      OrclUF.forge(pk, m, s);
      b <@ O.verify(pk, m, s);
      return b;
    }
  }.
  
  local lemma lem1 &m :
    Pr[IndSig(RealSigServ, A).main() @ &m : res] =
    Pr[IndSig(Wrap(RealSigServ), A).main() @ &m : res].
  proof.
    byequiv => //. 
    proc; inline *; call (_: ={glob RealSigServ});
       1: (by proc; inline *; sim); 
       1,2: by sim.
    + by proc; inline *; auto.
    by auto. 
  qed.

  local lemma lem2 &m :
    Pr[IndSig(IdealSigServ, A).main() @ &m : res] =
    Pr[IndSig(Wrap(IdealSigServ), A).main() @ &m : res].
  proof.
    byequiv => //. 
    proc; inline *; call (_: ={glob RealSigServ}); 
       1: (by proc; inline *; sim); 
       1,2: by sim.
    + by proc; inline *; auto.
    by auto.
  qed.

  local lemma lem3 &m :
    Pr[UF(MkAdvUF(A)).main() @ &m : res] = 
    Pr[IndSig(Wrap(RealSigServ), A).main() @ &m : OrclUF.forged].
  proof.
    byequiv => //. 
    proc; inline *; sp. 
    call (_: ={glob RealSigServ, glob OrclUF}); 2, 3: by sim.
    + by proc; inline *; sim.
    + by proc; inline *; auto => /> &m2; rewrite mem_fdom.
    by auto.
  qed.

  (* TODO: I would like to declare this operator as local,
     and to not see it outside the section *)
  op valid (pks_sks: (pkey, skey) fmap) (qs : (pkey * message * signature) fset) = 
    (forall pk sk, pks_sks.[pk] = Some sk => (pk,sk) \in keygen) /\
    (forall pk m s, (pk,m,s) \in qs =>
       exists sk, (pk,sk) \in keygen /\ s \in sign(sk,m)).

  lemma ind_uf &m : 
    (forall (O <: OrclInd{A}),
       islossless O.keygen => islossless O.sign =>
       islossless O.pkeys => islossless O.verify => islossless A(O).main) =>
    `| Pr[IndSig(RealSigServ, A).main() @ &m : res] -
       Pr[IndSig(IdealSigServ, A).main() @ &m : res] | <=
     Pr[UF(MkAdvUF(A)).main() @ &m : res].
  proof.
    move=> All;rewrite (lem1 &m) (lem2 &m) (lem3 &m) StdOrder.RealOrder.distrC.
    byequiv : (OrclUF.forged)=> // [ | ?? [->] /= h /h -> //].
    proc; inline *.
    call (_: OrclUF.forged, 
             ={glob RealSigServ, glob OrclUF} /\ 
               valid RealSigServ.pks_sks{1} RealSigServ.qs{1},
             ={OrclUF.forged}).
    + by conseq |>; proc; sp; if; 
         1: (by move => *; progress => /#);
         by auto => />; smt(get_setE).
    +  move => ??; conseq |>; proc; sp; if; auto => />; smt(keygen_ll). 
    + by move => ?; conseq |>; proc; sp; if; auto => />; smt(keygen_ll). 
    + conseq |>; proc; sp; if; 1: smt().
        if;
           1: smt(); 
           by auto => />; smt(verify_sign in_fsetU1). 
        by auto => /> /#.
    + move => ??; conseq |>; proc; sp; if; auto => />. 
       if; first by move => *; auto => />; smt(sign_ll). 
       by auto.
    + move => ?; conseq |>; proc; sp; if; auto => />. 
       if; first by auto => />; smt(sign_ll). 
       by auto.
    + by conseq />; conseq />; sim.
    + by move=> ??; conseq />; islossless.
    + by move=> ?; conseq />; islossless.
    + proc;inline *; auto => />; smt (verify_sign).
    + by move=> ? ->;proc; inline *;auto.
    + by move=> ?; proc; inline *; auto => />.
    auto => />; smt (in_fset0 emptyE).
  qed.

end section.

(* ------------------------------------------------------------------------- *)
(* We show that UF reduce to UF1                                             *)
(* ------------------------------------------------------------------------- *)

module type OrclUF1 = {
  proc sign (m:message) : signature
  proc forge(m:message, s:signature): unit
}.

module type AdvUF1 (O:OrclUF1) = {
  proc main(pk:pkey) : unit
}.

op q_sig1 = q_sig.

module UF1 (A:AdvUF1) = {
  var forged : bool
  var pk: pkey
  var sk: skey
  var qs: (message * signature) fset
  var count_sig : int

  module O = {
    proc init () = {
      forged <- false;
      qs <- fset0;
      count_sig <- 0;
      (pk,sk) <$ keygen;
    }

    proc sign (m:message) = {
      var s;
      s <- witness;
      if (count_sig < q_sig1) {
         s <$ sign (sk, m);
         qs <- qs `|` fset1 (m,s);
         count_sig <- count_sig + 1;
      }
      return s;
    }

    proc forge (m:message, s:signature) = {
     forged <- forged || ( verify (pk, m, s) /\ ! (m,s) \in qs ); 
    }
  }
 
  proc main () = {
    O.init();
    A(O).main(pk);
    return forged;
  }
}.

abstract theory UF1_UF.

  module (WAkg (A:AdvUF) : AdvUF) (O:OrclUF) = {
    var c: int
    module WO : OrclUF = {
      proc keygen() = {
        var pk <- witness;
        if (c < q_gen) {
          pk <@ O.keygen();
          c <- c + 1;
        }
        return pk;
      }

      include O [sign, pkeys, forge]

    }

    proc main() = {
      c <- 0;
      A(WO).main();
    }

  }.    

  module MkAdvUF1(A:AdvUF) (O:OrclUF1) = {
     var i : int
     var pki : pkey
     var mpki : (pkey, int) fmap
     var count_sig : int

     module WO = {
       proc keygen () = {
         var pk <- witness;
         if (WAkg.c < q_gen) {
           if (WAkg.c = i) {
              if (RealSigServ.count_pk < q_gen) {
                 pk <- pki;
                 RealSigServ.count_pk <- RealSigServ.count_pk + 1;
              }
           }
           else pk <@ OrclUF.keygen();
           if (pk \notin MkAdvUF1.mpki) MkAdvUF1.mpki.[pk] <- WAkg.c;
           WAkg.c <- WAkg.c + 1;
         }
         return pk;
       }

       proc sign(pk : pkey, m : message) : signature option = {
         var so : signature option <- None;
         var s : signature;
         if (count_sig < q_sig) {
            if (mpki.[pk] = Some i) {
                if (RealSigServ.count_sig < q_sig) {
                   s <@ O.sign(m);
                   so <- Some s;
                   RealSigServ.count_sig <- RealSigServ.count_sig + 1;
                 }
            }
            else so <@ RealSigServ.sign(pk,m);
            count_sig <- count_sig + 1;
         }
         return so;
       }

       proc pkeys () = {
         var s;
         s <@ RealSigServ.pkeys();
         return if mpki.[pki] = Some i then s `|` fset1 pki else s;
       }
  
       proc forge (pk:pkey, m:message, s:signature) = {
          if (mpki.[pk] = Some i) O.forge(m, s);
       }
     }

     proc main(pk:pkey) = {
       count_sig <- 0;
       pki <- pk;
       i <$ [0..q_gen-1]; 
       mpki <- empty;
       WAkg.c <- 0;
       RealSigServ.init();
       A(WO).main();
    }
        
  }.

  section.

    declare module A : AdvUF { RealSigServ, OrclUF, UF1, UF, WAkg, MkAdvUF1 }.

    local module Aux (O:OrclUF) = {
      var forged : int option

      module WO = {
        proc keygen () = {
          var pk <- witness;
          if (WAkg.c < q_gen) {
            pk <@ O.keygen();
            if (! pk \in MkAdvUF1.mpki) MkAdvUF1.mpki.[pk] <- WAkg.c;
            WAkg.c <- WAkg.c + 1;
          }
          return pk;
        }

        include O [sign, pkeys]

        proc forge (pk:pkey, m:message, s:signature) = {
          if (forged = None /\ is_forgery pk m s RealSigServ.pks_sks RealSigServ.qs)
            forged <- MkAdvUF1.mpki.[pk];
        }
      }

      proc main() = {
        forged <- None;
        MkAdvUF1.count_sig <- 0;
        MkAdvUF1.mpki <- empty;
        WAkg.c <- 0;
        A(WO).main();
      }
    }.

    local lemma UF_Aux &m : 
      Pr[UF(WAkg(A)).main() @ &m : res] = 
        Pr[UF(Aux).main() @ &m : exists i, 0 <= i < q_gen /\ Aux.forged = Some i].
    proof.
      byequiv (_: ={glob A} ==> 
        res{1} = exists i, 0 <= i < q_gen /\ Aux.forged{2} = Some i) => //.
      proc; inline *.
      call (_: ={glob RealSigServ, glob WAkg} /\
               (forall pk, pk \in MkAdvUF1.mpki = pk \in RealSigServ.pks_sks){2} /\
               (forall pk, pk \in MkAdvUF1.mpki => 
                  exists i, 0 <= i < q_gen /\ MkAdvUF1.mpki.[pk] = Some i){2} /\
               (forall i, Aux.forged = Some i => 0 <= i < q_gen){2} /\
               (OrclUF.forged{1} = (Aux.forged{2} <> None)) /\
               (0 <= WAkg.c <= q_gen){2} /\
               WAkg.c{1} = RealSigServ.count_pk{2} /\
               (0 <= RealSigServ.count_pk{1} <= q_gen)) => /=.
      + proc; inline *. sp;if => //=.
        sp;if. auto => />. 
        auto => />. progress;
            1: (by smt (mem_set get_setE));
            1: (by case (pk1 = pk0skL.`1); 
                   1: (by smt(mem_set get_setE));
                   move => *;move : (H0 pk1); smt(mem_set get_setE));
            smt(mem_set get_setE).
        wp;skip;progress;smt().
      + by conseq />; sim.
      + by conseq />; sim.
      + (* TODO: conseq (_ : #[/1:3]post  *)
        proc.
        (* FIXME: conseq /> *)
        conseq (_ : _ ==> OrclUF.forged{1} = (Aux.forged{2} <> None) /\
          (forall (i : int), Aux.forged{2} = Some i => 0 <= i < q_gen)); 1: smt ().
        auto => /#.
       auto => />;smt(emptyE lt0_q_gen). 
    qed.

    local clone import PlugAndPray with
      type tval <- int,
      op indices <- range 0 q_gen,
      type tin <- unit,
      type tres <- bool
      proof *.
    realize indices_not_nil. by smt(size_range lt0_q_gen). qed.

    local lemma Aux_bound &m : 
       Pr[UF(Aux).main() @ &m : (exists i, 0 <= i < q_gen /\ Aux.forged = Some i)] = 
       q_gen%r * Pr[Guess(UF(Aux)).main() @ &m :
          (exists i, 0 <= i < q_gen /\ Aux.forged = Some i) /\
          res.`1 = odflt 0 Aux.forged].
    proof.
      pose phi (g:glob UF(Aux)) (_:bool) := 
        (exists i, 0 <= i < q_gen /\ g.`1 = Some i).
      pose psi (g:glob UF(Aux)) (_:bool) := odflt 0 g.`1.
      have Hpsi: forall g o, phi g o => psi g o \in range 0 q_gen.
      + by move=> g ? [i [h heq]];rewrite /psi heq /= mem_range.
      have := PBound (UF(Aux)) phi psi () &m Hpsi.  
      have -> : size (undup (range 0 q_gen)) = q_gen.   
      + rewrite undup_id 1:range_uniq size_range; smt (lt0_q_gen).
      rewrite /phi /psi /=; smt (lt0_q_gen).
    qed.

    local clone import PROM.GenEager as Eager with 
      type from <- unit,
      type to <- pkey * skey,
      op sampleto <- fun (_:unit) => keygen,
      type input <- unit,
      type output <- bool
      proof *. 
      realize sampleto_ll. 
      proof. by solve (random). qed.

    local module Aux1(RO:RO) = {
      module WO = {
        proc keygen () = {
          var sk;
          var pk <- witness;
          if (WAkg.c < q_gen) {
            if (WAkg.c = MkAdvUF1.i) {
              if (RealSigServ.count_pk < q_gen) {
                 (pk, sk) <@ RO.get();
                 if (pk \notin RealSigServ.pks_sks) RealSigServ.pks_sks.[pk] <- sk;  
                 RealSigServ.count_pk <- RealSigServ.count_pk + 1;
              }
            }
            
            else pk <@ OrclUF.keygen();
            if (! pk \in MkAdvUF1.mpki) MkAdvUF1.mpki.[pk] <- WAkg.c;
            WAkg.c <- WAkg.c + 1;
          }
          return pk;
        }

        include OrclUF [sign, pkeys]

        proc forge (pk:pkey, m:message, s:signature) = {
          if (MkAdvUF1.mpki.[pk] = Some MkAdvUF1.i) 
            UF1.forged <- UF1.forged || is_forgery pk m s RealSigServ.pks_sks RealSigServ.qs;
        }
      }

      proc distinguish() = {
        RO.init();
        RO.sample();
        MkAdvUF1.i <$ [0..q_gen-1]; 
        UF1.forged <- false;
        MkAdvUF1.count_sig <- 0;
        MkAdvUF1.mpki <- empty;
        WAkg.c <- 0;
        RealSigServ.init();
        A(WO).main();
        return true;
      }
        
    }.

    local lemma Aux_Aux1 &m: 
      Pr[Guess(UF(Aux)).main() @ &m :
         (exists i, 0 <= i < q_gen /\ Aux.forged = Some i) /\
         res.`1 = odflt 0 Aux.forged] <= 
      Pr[Aux1(LRO).distinguish() @ &m : UF1.forged].
    proof.
      byequiv=> //; proc.
      inline *. swap{1} 13-12;wp.
      seq 1 3: (={glob A} /\ i{1} = MkAdvUF1.i{2} /\ 0 <= i{1} < q_gen /\ RO.m{2} = empty).
      + rnd;auto => />; smt (supp_dinter).
      conseq (_: (Aux.forged{1} = Some MkAdvUF1.i{2}) => UF1.forged{2}); 1: smt (). 
      call (_: ={RealSigServ.pks_sks, RealSigServ.qs, RealSigServ.count_sig, RealSigServ.count_pk, WAkg.c, MkAdvUF1.mpki} /\ 
               (WAkg.c <= MkAdvUF1.i => RO.m = empty){2} /\ 
               (Aux.forged{1} = Some MkAdvUF1.i{2} => UF1.forged{2})); last by auto.
      + proc;sp 1 1; if =>//;inline *;wp.
        if{2}; auto => />. 
        + smt(). 
        + sp; if;  auto => />.
          by smt(emptyE get_setE). 
        + by smt(emptyE get_setE).
        sp; if;auto; 1: smt ().
        by smt(emptyE get_setE).
      + by conseq />; sim.
      + by conseq />; sim.
      proc.
      if{1}; if{2};auto => /#.
    qed.
 
    local lemma Aux1_EAux1 &m: 
      Pr[Aux1(LRO).distinguish() @ &m : UF1.forged] =
      Pr[Aux1( RO).distinguish() @ &m : UF1.forged].
    proof. apply eq_sym; byequiv (RO_LRO_D Aux1) => //. qed.
 
    local lemma EAux1_MkAdvUF1 &m:
      Pr[Aux1( RO).distinguish() @ &m : UF1.forged] <=
      Pr[UF1(MkAdvUF1(A)).main() @ &m : res].
    proof.
      byequiv=> //; proc; inline *.
      call (_: (UF1.pk = MkAdvUF1.pki){2} /\
               ={ MkAdvUF1.i, MkAdvUF1.mpki, WAkg.c, RealSigServ.count_pk, RealSigServ.count_sig } /\
                RO.m{1} = empty.[tt <- (UF1.pk,UF1.sk){2}] /\
                RealSigServ.count_pk{1} = WAkg.c{1} /\
                RealSigServ.count_sig{1} = MkAdvUF1.count_sig{2} /\
                UF1.count_sig{2} <= RealSigServ.count_sig{2} /\
                (forall pk, pk \in MkAdvUF1.mpki = pk \in RealSigServ.pks_sks){1} /\
                (forall pk, 
                   if MkAdvUF1.mpki{2}.[pk] = Some MkAdvUF1.i{2} then
                      pk = UF1.pk{2} /\  RealSigServ.pks_sks{1}.[pk] = Some UF1.sk{2}
                   else RealSigServ.pks_sks{1}.[pk] = RealSigServ.pks_sks{2}.[pk]) /\
                RealSigServ.qs{1} = 
                 RealSigServ.qs{2} `|` image (fun (ms:_*_) => (UF1.pk{2}, ms.`1, ms.`2)) UF1.qs{2} /\
                (UF1.forged{1} => UF1.forged{2})).
      + proc; sp 1 1; if => //. 
        if => //; inline *;last first.
        sp;if => //; 1: by auto => />; smt(emptyE get_setE).
        auto => />. 
        if => //. 
        seq 4 1 : (#[/3:]pre /\ ={pk} /\ (pk,sk){1} = (UF1.pk,UF1.sk){2}).
        + conseq />; auto => />; smt (get_setE).
        swap {1} 2 -1. sp 1 1.
        if; 1: smt().
        + rcondt{1} 2;auto => />; smt (get_setE). 
        rcondf{1} 1;auto => />; by smt(get_setE).
        wp;skip;by smt(emptyE get_setE).
      + proc; sp 1 1; if => //; if{2}.
        + rcondt{2} 1; 1: by auto; smt().
        + rcondt{1} 1; 1: by auto; smt().
          inline *. 
        + rcondt{2} 3; 1: by auto; smt().
        auto => /> &m1 &m2 hpki _ hpk _ _ h.
        have := hpk pk{m2}; rewrite h /= => -[->> ->] /=; rewrite /oget /= /= => s -> /=.
          split; first by smt(emptyE get_setE).
          by rewrite imageU image1 /= fsetUA.
        inline *. sp 0 3. 
        + rcondt{2} 1; 1: by auto; smt().
        if; auto; 1: by smt().
        move=> /> &m1 &m2 hpki _ hpk _ _ h.
        have := hpk pk{m2}; rewrite h /= => -> /= ? s -> /=.
        split; first by smt(emptyE get_setE).
        smt (fsetUA fsetUC).  
        move=> /> &m1 &m2 hpki _ hpk _ _ h.
        by smt(emptyE get_setE).
      + proc; inline *;auto => /> &m1 &m2 hpki _ h _.
        case (MkAdvUF1.mpki{m2}.[MkAdvUF1.pki{m2}] = Some MkAdvUF1.i{m2}) => h1.
        + by apply fsetP => pk;rewrite in_fsetU in_fset1 !mem_fdom /#.
        by apply fsetP => pk;rewrite !mem_fdom /#.
      + proc;if => //; inline *; auto => /> &m1 &m2 hpki _ hpks hforge hpk. 
        rewrite /is_forgery; have := hpks pk{m2}; rewrite hpk /= /dom => -[->> ->] /=.
        rewrite in_fsetU imageP /= /#. 
      auto => />; rewrite mem_empty /= => -[??]??? /=; rewrite fset0U image0 /=; smt(mem_empty).
    qed.
 
    lemma uf_uf1 &m : Pr[UF(WAkg(A)).main() @ &m : res] <= q_gen%r * Pr[UF1(MkAdvUF1(A)).main() @ &m : res].
    proof.
      rewrite (UF_Aux &m) (Aux_bound &m).
      have := Aux_Aux1 &m; rewrite (Aux1_EAux1 &m); have := EAux1_MkAdvUF1 &m.
      smt (lt0_q_gen).
    qed.

  end section.

  lemma ind_uf1 (A <: AdvInd{RealSigServ, OrclUF, UF1, UF, WAkg, MkAdvUF1}) &m : 
    (forall (O <: OrclInd{A}),
       islossless O.keygen => islossless O.sign =>
       islossless O.pkeys => islossless O.verify => islossless A(O).main) =>
    `| Pr[IndSig(RealSigServ, A).main() @ &m : res] -
       Pr[IndSig(IdealSigServ, A).main() @ &m : res] | <=
     q_gen%r * Pr[UF1(MkAdvUF1(MkAdvUF(A))).main() @ &m : res].
  proof.
    move=> hll; have := ind_uf (A) &m _.
    + by move=> O hk hs hp hv; apply (hll O hk hs hp hv).
    have := uf_uf1 (MkAdvUF(A)) &m.
    have -> /# : Pr[UF(MkAdvUF(A)).main() @ &m : res] = 
                 Pr[UF(WAkg(MkAdvUF(A))).main() @ &m : res].
    byequiv => //; proc; inline *.
    call(_: ={glob OrclUF, glob RealSigServ} /\ WAkg.c{2} = RealSigServ.count_pk{2}).
    + proc;inline *.
      sp;if {2} => //=.
      + by sp; if => //=; auto => /#.
      by if {1} => //=; wp; rnd{1}; auto => />. 
    + proc;inline *.
      sp;if => //=.
      by sp;if => //=; auto => />.
    + by proc;inline*;auto. 
    + by proc;inline*;auto. 
    by auto.
  qed.

end UF1_UF.
