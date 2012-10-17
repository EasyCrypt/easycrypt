(* Modulus Length *)
cnst kBits : int.
axiom kBits_Pos: 0 <= kBits.

(* Conversion Operations *)
op OS2IP : bitstring{kBits} -> int.
op I2OSP : int -> bitstring{kBits}.

axiom OS2IP_range :
  forall (x: bitstring{kBits}),
    0 <= OS2IP(x) && OS2IP(x) < 2^kBits. 

axiom I2OSP_OS2IP :
  forall (x: bitstring{kBits}),
    I2OSP(OS2IP(x)) = x.

axiom OS2IP_I2OSP :
  forall (x: int), 0 <= x => x < 2^kBits =>
    OS2IP(I2OSP(x)) = x.

(* The RSA permutation *)
type keypair = int * int * int.
op valid_keypair : (int, int, int) -> bool.

op valid_pkey : (int, int) -> bool.
axiom valid_pkey_pair : forall (n, e, d:int),
  valid_keypair(n, e, d) => valid_pkey(n, e).

op valid_skey : (int, int) -> bool.
axiom valid_skey_pair : forall (n, e, d:int),
  valid_keypair(n, e, d) => valid_skey(n, d).

pop RSAGen : () -> int * int * int.
aspec RSAGen_valid() : ned = RSAGen() : 
 true ==> let n,e,d = ned in valid_keypair(n,e,d).

op RSAEP(n, e, x:int) = (x ^ e) % n.
op RSADP(n, d, x:int) = (x ^ d) % n.

axiom RSA_range : forall (n,e,m:int),
  valid_pkey(n,e) => 0 <= m => m < n =>
  0 <= RSAEP(n,e,m) && RSAEP(n,e,m) < n.

axiom RSA_inv_range : forall (n,d,c:int),
  valid_skey(n,d) => 0 <= c => c < n =>
  0 <= RSADP(n,d,c) && RSADP(n,d,c) < n.

axiom RSA_bijection : forall (n,e,d,m:int),
  valid_keypair(n,e,d) => 0 <= m => m < n =>
  RSADP(n,d,RSAEP(n,e,m)) = m.


(* RSA game on integers *)
adversary A(n, e, y:int): int { }.

game RSA_int = {
  abs A = A { }

  fun Main(): bool = {
    var n, e, d, r, r' : int;
    (n, e, d) = RSAGen();
    r = [0..n-1];
    r' = A(n, e, RSAEP(n, e, r));
    return (r = r');
  }
}.


(* RSA game on truncated bitstrings *)
op cons0 : bitstring{kBits - 8} -> bitstring{kBits}.

axiom OS2IP_cons0 :
  forall (x: bitstring{kBits - 8}),
    OS2IP(cons0(x)) <= 2^(kBits - 8). 

adversary A0(n, e:int, x:bitstring{kBits}): bitstring{kBits - 8} { }.

game RSA_bits = {
  abs A0 = A0 { }

  fun Main() : bool = {
    var n, e, d: int;
    var r, r' : bitstring{kBits - 8};
    var c : bitstring{kBits};
    (n, e, d) = RSAGen();
    r = {0,1}^(kBits - 8);
    c = let p = cons0(r) in I2OSP(RSAEP(n, e, OS2IP(p)));
    r' = A0(n, e, c);
    return (r = r');
  }
}.
