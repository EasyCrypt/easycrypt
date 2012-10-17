type group.

type secret_key = int.
type public_key = group.
type keys = secret_key * public_key.

type message = group.
type cipher = group * group.

cnst q:int.
cnst g:group.

op gmul : (group, group) -> group.
op [^] : (group, int) -> group as gpow.

adversary A1 (pk:public_key) : message * message  {}.
adversary A2 (pk:public_key, c:cipher) : bool {}.

game ElGamal = {

  fun KG() : keys = {
    var x : int = [0..q];
    return (x, g ^ x);
  }

  fun Enc(pk:public_key, m:message): cipher = {
    var y : int = [0..q];
    return (g ^ y, gmul (pk ^ y, m));
  }

  abs A1 = A1 {}

  abs A2 = A2 {}
  
  fun Main():bool = {
    var sk : secret_key;
    var pk : public_key;
    var m0, m1, mb : message;
    var b, b' : bool;
    var c : cipher;

    (sk,pk) = KG();
    (m0,m1) = A1(pk);
     b = {0,1};
     mb = b ? m0 : m1;
     c = Enc(pk, mb);
     b' = A2(pk,c);
     return b = b' ;
  }

}.

game ElGamal0 =
  ElGamal where Main = {
    var x : int = [0..q];
    var sk : int = x;
    var pk : public_key = g ^ sk;
    var m0, m1, mb : message;
    var y : int;
    var b, b' : bool;
    var c : cipher;

    (m0,m1) = A1(pk);
    b = {0,1};
    mb = b ? m0 : m1;
    y = [0..q];
    c = (g ^ y, gmul (pk ^ y, mb));
    b' = A2(pk,c);
    return b = b' ;
  }.

game ElGamal1 = {
  fun KG = ElGamal.KG
}.

equiv equiv_0: ElGamal.Main ~ ElGamal0.Main : true ==> res{1} = res{2} by auto.

claim Fact1 : ElGamal.Main[res] = ElGamal0.Main[res] 
using equiv_0.
