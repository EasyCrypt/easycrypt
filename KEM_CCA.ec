require import Bool Core Int List Distr.
require import DBool.

type pkey, skey, Key, encap.

op dkey : Key distr.

module type Scheme = {
  (* Key generation *)
  proc kg () : pkey * skey

  (* Encapsulation algorithm *)
  proc encap (pk : pkey) : Key * encap

  (* Decapsulation algorithm: deterministic, and may fail. *)
  proc decap (sk : skey, c : encap) : Key option
}.

module type Dec_OracleT = {
  proc dec_orcl (c : encap) : Key option
}.

module type Adversary (S : Scheme) (D : Dec_OracleT) = {
  proc guess(pk : pkey, c : encap, k : Key) : bool
}.


module Dec_Oracle (S : Scheme) = {
  var sk : skey
  var c0 : encap
  
  proc init (sk : skey, c0 : encap) = {
    c0 <- c0;
    sk <- sk;
  }
  
  proc dec_orcl (c : encap) = {
    var k = None;

    if (c <> c0) {
      k <@ S.decap(sk, c);
    }

    return k;
  }
}.

module CCA (S:Scheme) (A:Adversary) = {
  proc main() : bool = {
    var pk, sk, k0, k1, c, b, b';

    (pk, sk) <- S.kg();
    (k0, c)   <- S.encap(pk);
    k1       <$ dkey;
    b        <$ {0,1};

    Dec_Oracle(S).init(sk, c);
    b'       <@ A(S, Dec_Oracle(S)).guess(pk, c, b ? k0 : k1);
    return (b' = b);
  }
}.
