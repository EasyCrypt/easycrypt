require import Bool.

type pkey.
type skey.
type plaintext.
type ciphertext.

module type Scheme = {
 fun kg() : pkey * skey 
 fun enc(pk:pkey, m:plaintext)  : ciphertext 
 fun dec(sk:skey, c:ciphertext) : plaintext
}.

module type Adversary = {
 fun choose(pk:pkey)     : plaintext * plaintext 
 fun guess(c:ciphertext) : bool                  
}.

module type Init = {
 fun init() : unit
}.

module CPA (S:Scheme, A:Adversary, I:Init) = {
  fun main() : bool = {
    var pk : pkey;
    var sk : skey;
    var m0, m1 : plaintext;
    var c : ciphertext;
    var b, b' : bool;

    I.init();
    (pk, sk) = S.kg();
    (m0, m1) = A.choose(pk);
    b        = ${0,1};
    c        = S.enc(pk, b ? m1 : m0);
    b'       = A.guess(c);
    return (b' = b);
  } 
}.

module Correctness (S:Scheme, I:Init) = {
  fun main(m:plaintext) : bool = {
    var pk : pkey;
    var sk : skey;
    var c  : ciphertext;
    var m' : plaintext;

    I.init();
    (pk, sk) = S.kg();
    c        = S.enc(pk, m);
    m'       = S.dec(sk, c); 
    return (m' = m);
  }
}.
