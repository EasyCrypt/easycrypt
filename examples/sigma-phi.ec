(*
** Completeness, Soundness and Zero-Knowledge of a generic Sigma-phi protocol
*)


(** Modulo arithmetic *)

op [%%] : (int,int) -> int as mod_int.

axiom mod_small : forall (x:int,n:int), 0 <= x => x < n => x %% n = x.

axiom mod_add : forall (x,y,n:int), 0 <  n => (x %% n + y) %% n = (x + y) %% n.

axiom mod_bound : forall (x:int,n:int), 0 < n => 0 <= x %% n && x %% n < n.
 

(** Source group -- additive notation *)
type G. 

cnst q : int. (* Order *)
cnst g : G.   (* Generator *)
cnst e : G.   (* Identity element *)

op [+] : (G, G) -> G   as G_law. 
op [*] : (G, int) -> G as G_pow. 
op [-] : G -> G        as G_inv. 
op log : G -> int. (* discrete log base g *)

axiom q_pos : 0 < q.

axiom G_law_assoc : forall (x,y,z:G), (x + y) + z = x + (y + z).

axiom G_inv_spec : forall (x:G), x + -x = e && -x + x = e.

axiom G_id_spec : forall (x:G), x + e = x && e + x = x.

axiom G_log_spec : forall (x:G), g * log(x) = x.

axiom G_pow_plus : forall (x:G, a,b:int), x * (a + b) = x * a + x * b.

axiom G_pow_distr : forall (x,y:G, a:int), (x + y) * a = (x * a) + (y * a).

axiom G_pow_pow : forall (x:G, a,b:int), (x * a) * b = x * (a * b).

axiom G_pow_mod : forall (z:int), g * (z%%q) = g * z.

(** Target group -- multiplicative notation *)
type H.

cnst eH : H. (* Identity element *)

op [*] : (H, H) -> H   as H_law. 
op [^] : (H, int) -> H as H_pow.
op inv : H -> H.

axiom H_law_assoc : forall (x,y,z:H), (x * y) * z = x * (y * z).

axiom H_inv_spec : forall (x:H), x * inv(x) = eH && inv(x) * x = eH.

axiom H_id_spec : forall (x:H), x * eH = x && eH * x = x.

axiom H_pow_plus : forall (x:H, a,b:int), x ^ (a + b) = (x ^ a) * (x ^ b).

axiom H_pow_distr : forall (x,y:H, a:int), (x * y) ^ a = (x ^ a) * (y ^ a).

axiom H_pow_pow : forall (x:H, a,b:int), (x ^ a) ^ b = x ^ (a * b).

axiom H_inv_pow : forall (x:H, a:int), inv(x) = x ^ (-1).

axiom H_pow_zero: forall (x:H), x ^ 0 = eH.

axiom H_pow_one : forall (x:H), x ^ 1 = x.

axiom H_pow_inv : forall (x:H, a:int), inv(x ^ a) = inv(x) ^ a.

axiom H_inv_mul : forall (x,y:H), inv(x * y) = inv(y) * inv(x).


(** Special homomorphism *)
op phi : G -> H.
op u : H -> G.

cnst v : int. (* Special exponent *)

axiom v_nonzero : v <> 0.

axiom phi_homomorphic     : forall (x,y:G), phi(x + y) = phi(x) * phi(y).

axiom phi_homomorphic_pow : forall (x:G, a:int), phi(x * a) = phi(x) ^ a.

axiom phi_homomorphic_inv : forall (x:G), phi(-x) = inv(phi(x)).

axiom phi_special : forall (x:H), phi(u(x)) = x ^ v.


(* Challenge set *)
cnst cplus : int. (* Size, i.e. C = [0..cplus-1] *)

op gcd : (int, int) -> int.

axiom cplus_spec : forall (c:int), -cplus <= c && c <= cplus => gcd(c, v) = 1.


(* The protocol *)

op R(x:H, w:G) = x = phi(w). (* Knowledge relation *)

game Protocol = {
  fun P1(x:H, w:G) : H * G = {
    var a : int = [0..q-1];
    var y : G = g * a;
    return (phi(y), y);    
  }

  fun V1(x:H, r:H) : int = {
    var c : int  = [0..cplus];
    return c;
  }

  fun P2(x:H, w:G, y:G, c:int) : G = {
    return (y + (w * c));
  }

  fun V2(x:H, r:H, c:int, s:G) : bool = {
    return (phi(s) = r * (x ^ c));
  }

  fun Main(x:H, w:G) : bool = {
    var y, s : G;
    var r : H;
    var c : int;
    var b : bool;
    (r, y) = P1(x, w);
    c = V1(x, r);
    s = P2(x, w, y, c);
    b = V2(x, r, c, s);
    return b;   
  }
}.

prover "alt-ergo".


(* Completeness *)

game Trivial = { fun Main() : bool = { return true; } }.

equiv completeness : Protocol.Main ~ Trivial.Main : R(x,w){1} ==> ={res} by auto.


(* Special Soundness *)

op egcd : (int, int) -> (int * int * int).

axiom egcd_spec : forall (x,y:int), 
  let a, b, d = egcd(x, y) in d = gcd(x, y) && x * a + y * b = d.

game Extract = {
  var x : H

  fun KE(r:H, c1,c2:int, s1,s2:G) : G = {
    var a, b, d : int;
    (a, b, d) = egcd(c1 - c2, v);
    return ((-s2 + s1) * a + u(x) * b);
   }
}.

(* 2-extractability *)
equiv soundness : Extract.KE ~ Trivial.Main :
 (0 <= c1 && c1 <= cplus && 0 <= c2 && c2 <= cplus){1} &&
 (phi(s1) = r * (x ^ c1) && phi(s2) = r * (x ^ c2) && c1 <> c2){1} ==> 
 R(x{1}, res{1}).
proof.
 wp.
 app 0 0 
   (-cplus <= c1 - c2 && c1 - c2 <= cplus &&
    let a,b,d = egcd(c1 - c2, v) in
    phi((-s2 + s1) * a + u(x) * b) =
    inv(x ^ c2) ^ a * inv(r) ^ a * r ^ a * x ^ (c1 * a) * x ^ (v * b)){1}.
 trivial.
 app 0 0 
   (let a,b,d = egcd(c1 - c2, v) in
    d = 1 && phi((-s2 + s1) * a + u(x) * b) = x ^ ((-c2 + c1) * a + v * b)){1}.
 trivial.
 app 0 0 (let a,b,d = egcd(c1 - c2, v) in phi((-s2 + s1) * a + u(x) * b) = x){1}.
 trivial.
 trivial.
save.


(* Special Honest-Verifier Zero-Knowledge *)

(* Like Protocol, but for a fixed challenge *)
game Protocol' = {
  fun P1(x:H, w:G) : H * G = {
    var a : int = [0..q-1];
    var y : G = g * a;
    return (phi(y), y);    
  }

  fun P2(x:H, w:G, y:G, c:int) : G = {
    return (y + (w * c));
  }

  fun V2(x:H, r:H, c:int, s:G) : bool = {
    return (phi(s) = r * (x ^ c));
  }

  fun Main(x:H, w:G, c:int) : H * int * G = {
    var y, s : G;
    var r : H;
    var b : bool;
    (r, y) = P1(x, w);
    s = P2(x, w, y, c);
    b = V2(x, r, c, s);
    return (r, c, s);   
  }
}.

game Simulation = {
  fun S(x:H, c:int) : H * int * G = {
    var a : int = [0..q-1];
    var s : G = g * a;
    var r : H = phi(s) * inv(x ^ c);
    return (r, c, s);
  }
}.

equiv SHVZK : Simulation.S ~ Protocol'.Main : ={x,c} && R(x{2}, w{2}) ==> ={res}.
proof.
 inline; wp.
 rnd ((a + - log(w{2}) * c{2}) %% q),  ((a + log(w{2}) * c{2}) %% q); trivial.
save.
