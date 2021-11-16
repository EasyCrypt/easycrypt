require import AllCore FSet SmtMap Distr.
(* Formalisation of collision resistance:
     CR : Collision resistance game 
     RealHash/IdealHash: 
        Collision resistance expressed in term 
        indistinghuishability game *)

type hkey.
op hkgen : hkey distr.
axiom hkgen_ll : is_lossless hkgen.
type domain.
type range.

(* hash function  *)
op hash : hkey -> domain -> range.

type data.

(* Definition of collision resistance *)

op q_col : int.

module type OrclCR = {
  proc collision(m1 : domain option, m2 : domain option): unit
}.

module type AdvCR (O:OrclCR) = {
  proc main(hk : hkey) : unit
}.

module OrclCR : OrclCR = {

  var col_found : bool
  var col_count : int
  var hk : hkey

  proc init() : unit = { hk <$ hkgen; col_found <- false; col_count <- 0; }

  proc collision(m1 : domain option, m2 : domain option) = {
    if (col_count < q_col) {
       if (m1 <> None && m2 <> None) {
          col_found <- col_found || 
               ( m1 <> m2 /\ hash hk (oget m1) = hash hk (oget m2)); 
       }
       col_count <- col_count + 1;
    }
  }
}.

module CR (A:AdvCR) = {

  proc main () = {
    OrclCR.init();
    A(OrclCR).main(OrclCR.hk);
    return OrclCR.col_found;
  }

}.

(* Formalization of an ideal hash *)

module type Hash = {
   proc init() : unit
   proc hash(p : domain) : range
}.

module type HCheck = {
   proc check(p : domain, h : range) : bool
}.

module type HashI = {
   proc init() : unit
   proc hash(p : domain) : range option
   proc check(p : domain, h : range) : bool
}.

op q_hash = q_col.

module RealHash = {
   var pres : (range,domain) fmap
   var count_hash : int
   var hk : hkey

   proc init () = { 
        hk <$ hkgen;
        pres <- empty; 
        count_hash <- 0;
   }

   proc hash(p : domain) : range option = {
        var h, ho;
        ho <- None;
        if (count_hash < q_hash) {
           h <- hash hk p;
           ho <- Some h;
           if (h \notin pres) {
                pres.[h] <- p;
           }
           count_hash <- count_hash + 1;
        }
        return ho;
   }

   proc check(p : domain, h : range) : bool = {
        var b;
        b <- witness;
        if (count_hash < q_hash) {
           b <- h = hash hk p;
           count_hash <- count_hash + 1;
        }
        return b;
   }

}.

module IdealHash = {
   include RealHash [init]

   proc hash(p : domain) : range option = {
        var h,ho;
        ho <- None;
        if (RealHash.count_hash < q_hash) {
           h <- hash RealHash.hk p;
           ho <- Some h;  
           if (h \notin RealHash.pres) {
                RealHash.pres.[h] <- p;
           }
           else {
              if (Some p <> RealHash.pres.[h]) {
                 ho <- None;
              }
           }
           RealHash.count_hash <- RealHash.count_hash + 1;
        }
        return ho;
   }

   proc check(p : domain, h : range) : bool = {
        var b;
        b <- witness;
        if (RealHash.count_hash < q_hash) {
           if (h \in RealHash.pres) {
              b <- hash RealHash.hk p = h && Some p = RealHash.pres.[h];
           }
           else {
              b <- hash RealHash.hk p = h;
           }
           RealHash.count_hash <- RealHash.count_hash + 1;
        }
        return b;
   }

}.

(* ----------------------------------------------------------------------------- *)
(* We prove that for all adversaries which is able to distinguish between        *)
(* RealHash and IdealHash there exists a adversary which is able to win    *)
(* the collision resistance game.                                                      *)
(* ----------------------------------------------------------------------------- *)

module type OrclInd = {
   proc hash(p : domain) : range option
   proc check(p : domain, h : range) : bool
}.

module type AdvInd(O:OrclInd) = {
  proc main (hk : hkey) : bool
}.

module IndHash (O:HashI, A:AdvInd) = {
  proc main() : bool = {
    var b;
    O.init();
    b <@ A(O).main(RealHash.hk);
    return b;
  }
}.

module (MkAdvCR(A:AdvInd):AdvCR) (O:OrclCR) = {
    module OA = {
      include RealHash [-check,hash]

      proc hash(p : domain) : range option = {
        var h,ho;
        ho <- None;
        if (RealHash.count_hash < q_hash) {
           h <- hash RealHash.hk p;
           ho <- Some h;  
           if (h \notin RealHash.pres) {
                RealHash.pres.[h] <- p;
           }
           O.collision(RealHash.pres.[h],Some p);
           RealHash.count_hash <- RealHash.count_hash + 1;
        }
        return ho;
      }

      proc check(p : domain, h : range) : bool = {
        var b;
        b <- witness;
        if (RealHash.count_hash < q_hash) {
           b <- h = hash RealHash.hk p;
           O.collision(RealHash.pres.[h],Some p);
           RealHash.count_hash <- RealHash.count_hash + 1;
        }
        return b;

      }
    }
    
    proc main (hk : hkey) = {
      var b;
      OA.init();
      RealHash.hk <- hk;
      b <@ A(OA).main(RealHash.hk);
    }
  }.

section.

  declare module A <: AdvInd { RealHash, OrclCR}.
  
  declare axiom Alossless :
    forall (O <: OrclInd{A}),
          islossless O.hash => 
          islossless O.check => islossless A(O).main.

  local module Wrap (O:HashI) = { 
      var flag : bool

      proc init():unit =  { O.init(); OrclCR.init(); RealHash.hk <- OrclCR.hk; flag <- false; }
      proc hash(p : domain) : range option = {
        var h;
        h <@ O.hash(p);
        if (!flag) {
           OrclCR.collision(RealHash.pres.[hash RealHash.hk p],Some p);
           if (RealHash.count_hash = q_hash) {
              flag <- true;
           }
        }
        return h;
      }
      proc check(p : domain, h : range) : bool = {
        var b;
        b <@ O.check(p,h);
        if (!flag) {
           OrclCR.collision(RealHash.pres.[h],Some p);
           if (RealHash.count_hash = q_hash) {
              flag <- true;
           }
        }
        return b;
      }
  }.
  
  local lemma lem1 &m :
    Pr[IndHash(RealHash, A).main() @ &m : res] =
    Pr[IndHash(Wrap(RealHash), A).main() @ &m : res].
  proof.
    byequiv => //. 
    proc; inline *; call (_: ={glob RealHash} /\ 
            (Wrap.flag{2} => RealHash.count_hash{1} = q_hash));
     1..2: by proc; inline *; wp; skip => /#.
    by wp;rnd;wp;rnd{2};auto => /> *; apply hkgen_ll.
  qed.

  local lemma lem2 &m :
    Pr[IndHash(IdealHash, A).main() @ &m : res] =
    Pr[IndHash(Wrap(IdealHash), A).main() @ &m : res].
  proof.
    byequiv => //. 
    proc; inline *; call (_: ={glob RealHash} /\ 
           (Wrap.flag{2} => RealHash.count_hash{1} = q_hash));
      1..2: by  proc;inline *;wp;skip => /#. 
    by wp;rnd;wp;rnd{2};auto => /> *; apply hkgen_ll.
  qed.

  local lemma lem3 &m :
    Pr[CR(MkAdvCR(A)).main() @ &m : res] = 
    Pr[IndHash(Wrap(RealHash), A).main() @ &m : OrclCR.col_found].
  proof.
    byequiv => //. 
    proc; inline *; sp. 
    call (_: ={glob OrclCR, glob RealHash} /\ 
           (Wrap.flag{2} => RealHash.count_hash{1} = q_hash) /\
              (OrclCR.col_count{1} = RealHash.count_hash{1}));
      1..2: by  proc;inline *;wp;skip => /#. 
    wp; conseq />. 
    swap {1} 5 -4.
    swap {2} 4 -2.
    by auto => />.
  qed.

  lemma ind_cr &m : 
    `| Pr[IndHash(RealHash, A).main() @ &m : res] -
       Pr[IndHash(IdealHash, A).main() @ &m : res] | <=
     Pr[CR(MkAdvCR(A)).main() @ &m : res].
  proof.
    rewrite (lem1 &m) (lem2 &m) (lem3 &m) StdOrder.RealOrder.distrC.
    byequiv : (OrclCR.col_found)=> // [ | ?? [->] /= h /h -> //].
    proc; inline *. sp.
    call (_:OrclCR.col_found, 
          ={glob OrclCR, glob RealHash, glob Wrap} /\ OrclCR.hk{2} = RealHash.hk{2} /\
          (forall h, h \in RealHash.pres{1} => hash RealHash.hk{1} (oget RealHash.pres{1}.[h]) = h) /\
           (Wrap.flag{2} => RealHash.count_hash{1} = q_hash) /\
              (OrclCR.col_count{1} = RealHash.count_hash{1}), 
          ={OrclCR.col_found});last first.
    + by auto => />;smt(emptyE).
    + by apply Alossless.
    + move => *;proc;inline *;auto => /> *; smt(get_setE). 
    + by move => *;proc;inline *;wp;skip => />; smt(get_setE).
    + by move => *;proc;inline *;wp;skip => />; smt(get_setE).
    + by move => *;proc;inline *;wp;skip => />; smt(get_setE).
    + by move => *;proc;inline *;wp;skip => />; smt(get_setE).
    by move => *;proc;inline *;wp;skip => />; smt(get_setE).
  qed.

end section.
