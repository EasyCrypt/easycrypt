(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2021 - Inria
 * Copyright (c) - 2012--2021 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

require import AllCore FSet List SmtMap Distr DBool.

(*******************************************)
(*           Multirecipient PKE            *)
(*******************************************)

type Pk.
type Sk.
type CTxt.
type PTxt.
type Tag.

type MPk = Pk fset.
type MCTxt = (Pk,CTxt) fmap.

op gen : (Sk * Pk) distr.
axiom gen_ll : is_lossless gen.
op mencrypt( mpk : MPk, tag : Tag, ptxt : PTxt) : (MCTxt) distr.
axiom mencrypt_ll : forall mpk t txt, is_lossless (mencrypt mpk t txt).
op decrypt( sk : Sk, tag : Tag, ctxt : CTxt) : PTxt option.

op  q_maxpks : int.

hint solve 2 random : gen_ll mencrypt_ll.

module Scheme = {
 proc gen() : (Sk * Pk) = {
     var kpair;
     kpair <$ gen;
     return kpair;
 }
 proc mencrypt( mpk : MPk, tag : Tag, ptxt : PTxt) : MCTxt = {
     var cph;
     cph <$ mencrypt mpk tag ptxt;
     return cph;
 }
 proc decrypt( sk : Sk, tag : Tag, ctxt : CTxt) : PTxt option = {
     var msg;
     msg <- decrypt sk tag ctxt;
     return msg;
 }
}.

module type MRPKE_OrclT = {
  proc gen() : Pk
  proc lor (pks:MPk, tag : Tag, m0:PTxt, m1:PTxt) : MCTxt option
  proc dec (pk:Pk, tag : Tag, ctxt : CTxt) : PTxt option
}.

module type MRPKE_Adv(O:MRPKE_OrclT) = {
  proc guess() : bool
}.

op fold_encs(pks : MPk, tag : Tag, ctxts : (MCTxt)) =
   map (fun x, (x,tag,oget ctxts.[x])) (elems pks).  

op q_gen : int.
op q_lor : int.
op q_dec : int.

module MRPKE_lor = {
  
  module S = Scheme
  var b:bool
  var pklist : (Pk,Sk) fmap
  var lorlist : (Pk * Tag * CTxt) list
  var count_gen : int
  var count_lor : int
  var count_dec : int

  proc init(b : bool) = {
    MRPKE_lor.b <- b;
    pklist <- empty;
    lorlist <- [];
    count_gen <- 0;
    count_lor <- 0;
    count_dec <- 0;
  }
  
  proc gen () = {
    var k : Sk * Pk;
    var pk : Pk;
    pk <- witness;
    if (count_gen < q_gen) {
       k <@ S.gen();
       if (!(k.`2 \in pklist)) {
          pklist <- pklist.[k.`2 <- k.`1];
       }
       pk <- k.`2;
       count_gen <- count_gen + 1;
    }
    return pk;
  }

  proc lor (pks: MPk, tag : Tag, m0:PTxt, m1: PTxt) : MCTxt option = {
    var ro,r;

    ro <- None;

    if (count_lor < q_lor) {
       if (pks \subset fdom pklist /\ size (elems pks) < q_maxpks) {
         r <@ S.mencrypt(pks, tag, b ? m1 : m0);
         ro <- Some r;
         lorlist <- lorlist ++ (fold_encs pks tag r);
       }
       count_lor <- count_lor + 1;
    }
    return ro;
  }

  proc dec (pk : Pk, tag : Tag, ctxt : CTxt) : PTxt option = {
    var r;
    r <- None;
    if (count_dec < q_dec) {
       if ((pk \in fdom pklist)&&
           (!((pk,tag,ctxt) \in lorlist))) {
          r <@ S.decrypt(oget pklist.[pk],tag,ctxt);
       }
       count_dec <- count_dec + 1;
    }    
    return r;
  }
}.

module MRPKE_Sec (A:MRPKE_Adv) = {
  proc game(b : bool) = {
    var b';
    MRPKE_lor.init(b);
    b' <@ A(MRPKE_lor).guess ();
    return b';
  }

  proc main() = {
     var b,b';
     b <$ {0,1};
     b'<@ game(b);
     return (b = b');
  }
}.
