require import AllCore List FSet SmtMap Distr DBool DList.
(*require import AllCore Distr FSet SmtMap DBool. *)

type K.
type Msg.
type AData.
type Cph.

op gen : K distr.
axiom gen_ll : is_lossless gen.
op enc (k : K, a : AData, m : Msg) : Cph distr.
axiom enc_ll k a m : is_lossless (enc k a m).
op dec (k : K, a : AData, c : Cph) : Msg option.

axiom aead_corr ad msg key cph:
   cph \in enc key ad msg => dec key ad cph = Some msg.

module type AEAD_OraclesT = {
  proc newkey() : unit
  proc enc(kid : int, m : Msg, a : AData) : Cph option
  proc lor(kid : int, m0 m1 : Msg, a : AData) : Cph option
  proc dec(kid : int, a : AData, c : Cph) : Msg option
}.

module type AEAD_Adv(O : AEAD_OraclesT) = {
  proc guess() : bool
}.

module AEAD_Oracles : AEAD_OraclesT = {
  var cphlist : (int * AData * Cph) fset
  var keylist : (int,K) fmap
  var keycount : int
  var b : bool

  proc init() : unit = {
     b <$ {0,1};
     keycount <- 0;
     cphlist  <- fset0;
     keylist  <- empty;
  }

  proc newkey() : unit = {
     var key;
     key <$ gen;
     keylist.[keycount] <- key;
     keycount <- keycount + 1;
  }

  proc enc(kid : int, m : Msg, a : AData) : Cph option = {
     var c,co;
     co <- None;
     if (kid \in keylist) {
        c <$ enc (oget keylist.[kid]) a m;
        co <- Some c;
     }
     return co;     
  }

  proc lor(kid : int, m0 m1 : Msg, a : AData) : Cph option = {
     var c,co;
     co <- None;
     if (kid \in keylist) {
        c <$ enc (oget keylist.[kid]) a (if b then m1 else m0);
        cphlist <- cphlist `|` fset1 (kid,a,c);
        co <- Some c;
     }
     return co;     
  }

  proc dec(kid : int, a : AData, c : Cph) : Msg option = {
     var m;
     m <- None;
     if (kid \in keylist && !(kid,a,c) \in cphlist) {
         m <- if b then None else dec (oget keylist.[kid]) a c;
     }
     return m;
  }

}.

module AEAD_LoR(A : AEAD_Adv) = {
   module A = A(AEAD_Oracles)

   proc main() = {
      var b;
      AEAD_Oracles.init();
      b <@ A.guess();
      return b = AEAD_Oracles.b;
   }
}.

section CondProb.

module AEAD_OraclesCondProb : AEAD_OraclesT = {
  var cphlist : (int * AData * Cph) fset
  var keylist : (int,K) fmap
  var keycount : int

  include AEAD_Oracles [-init]

  proc init(bval:bool) : unit = {
     AEAD_Oracles.b <- bval;
     AEAD_Oracles.keycount <- 0;
     AEAD_Oracles.cphlist  <- fset0;
     AEAD_Oracles.keylist  <- empty;
  }
}.

module AEAD_LoRCondProb(A : AEAD_Adv) = {
   module A = A(AEAD_OraclesCondProb)

   proc game(b : bool) = {
     var b';

     AEAD_OraclesCondProb.init(b);
     b' <@ A.guess();
     return (b = b');
   }

   proc main() = {
      var b, adv;
      b <$ {0,1};
      adv <@ game(b);
      return adv;
   }
}.

declare module A : AEAD_Adv {AEAD_Oracles}.

equiv condprob_equiv : 
  AEAD_LoR(A).main ~ AEAD_LoRCondProb(A).main : 
  ={glob A} ==> ={res}.
proof.
  proc; inline*.
  wp.  
  call (_: ={glob AEAD_Oracles}).
    sim.
    sim.
    sim.
    sim.
  wp.
  rnd.
  skip => /#. 
qed.

end section CondProb.

op q_enc : int.
op q_lor : int.
op q_dec : int.
op q_maxn : int.

(* multiple encryption *)
op menc (keys: K list, tag : AData, ptxt : Msg) : Cph list distr =
   djoinmap (fun (k:K) => enc k tag ptxt) keys.

section AEADmul.


  module type AEADmul_OraclesT = {
    (* [lor] returns also the indexes of the new keys... *)
    proc lor (n : int, tag : AData, m0 : Msg, m1 : Msg) : ((int * Cph) list) option
    (* [dec] attempts to decypher with a given key index *)
    proc dec (id : int, tag : AData, ctxt : Cph) : Msg option
  }.

  module type AEADmul_Adv (O : AEADmul_OraclesT) = {
    proc guess () : bool
  }.


  module AEADmul_Oracles : AEADmul_OraclesT = {

    var b : bool
    var keys : K list
    var lorlist : (int * AData * Cph) list
    var n_keys : int
    var lorcount : int
    var deccount : int
    
    proc init () = {
      b <$ {0,1};
      keys <- [];
      n_keys <- 0;
      lorlist <- [];
      lorcount <- 0;
      deccount <- 0;
    }

    proc lor (n : int, aad : AData, m0 : Msg, m1 : Msg) : ((int * Cph) list) option = {
      var kidxs,new_keys,lctxt,olctxt;

      olctxt <- None;

      if (lorcount < q_lor && 0 <= n < q_maxn) {
        kidxs <- iota_ n_keys n;
        n_keys <- n_keys + n;
        new_keys <$ dlist gen n;
        keys <- keys ++ new_keys;
        lctxt <$ menc new_keys aad (if b then m1 else m0);
        olctxt <- Some (zip kidxs lctxt);
        lorlist <- lorlist ++ map (fun x:_*_ => (x.`1, aad, x.`2)) (zip kidxs lctxt);
        lorcount <- lorcount + 1;
      }

      return olctxt;
    }
    
    proc dec (id : int, tag : AData, ctxt : Cph) : Msg option = {
      var ptxt : Msg option;

      ptxt <- None;
      if (deccount < q_dec && 0 <= id < n_keys && !(id,tag,ctxt) \in lorlist){
        ptxt <- dec (nth witness keys id) tag ctxt;
        deccount <- deccount + 1;
      }
      return ptxt;
    }
  }.

  module AEADmul_Sec (A : AEADmul_Adv) = {
    module Or = AEADmul_Oracles

    proc main () : bool = {
      var b' : bool;
      var m0, m1, mb : Msg;
      var tag : AData;
      var c : Cph;
      
      Or.init();
      b' <@ A(Or).guess();

      return (AEADmul_Oracles.b = b');
    }
  }.

end section AEADmul.
