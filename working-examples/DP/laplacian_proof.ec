include "reals.ec".

(* op lap_op : (int, int, real, real) -> real. *)
(* axiom lap_op_def : forall (a:int,k:int,eps:real,res:real), *)
(*   lap_op(a,k,eps,res) = exp(-(|a%r-res|)/(k%r/eps)). *)

(* op lap_op (l:real,a:int,k:int,eps:real) = exp(-((|a%r-l|)/(k%r/eps))). *)
(* pop lap (a:int,k:int,eps:real) = (z:real) -> exp(-((|z-a%r|) / (k%r/eps) ) ). *)

cnst k : int.
axiom k_def : 0 < k.

cnst eps : real.
axiom eps_def : 0%r < eps.


(* real axioms *)


lemma real_auxlemma1 : forall (x,y,z:real), 0%r<=z && x<=y => x*z <= y*z.
lemma real_auxlemma4 : forall (x,y,z:real), 0%r<z && x<=y => x/z <= y/z.
lemma asd : forall(x,y:real), 0%r < y => x<=y => x/y <= 1%r.
axiom real_auxlemma10 : forall (x,y:real), x<>0%r => -y/x = -(y/x).


prover "alt-ergo", eprover, vampire, z3.

(* lap proof *)
timeout 60.
lemma asd''' : forall (a1:int,a2:int,res:real),
  |a1-a2| <= k => |a1%r-a2%r| <= k%r .
lemma lap_lem_aux1 : forall (a1:int,a2:int,res:real),
  |a1-a2| <= k =>
  (-(|a1%r-res|) + (|a2%r-res|))/ k%r <= 1%r.
lemma asd2 : forall(x,y:real), 0%r<=y => x<=1%r => x*y <= y.
lemma lap_lem_aux3 : forall (a1:int,a2:int,res:real),
  |a1-a2| <= k =>
   (-(|a1%r-res|) + |a2%r-res|)/k%r * eps <= eps.
unset lap_lem_aux1, asd2.
lemma lap_lem_aux4 : forall (a1:int,a2:int,res:real),
  |a1-a2| <= k =>
   (-(|a1%r-res|) + |a2%r-res|)/(k%r/eps) = (-(|a1%r-res|) + |a2%r-res|)/k%r * eps.
lemma lap_lem_aux6 : forall (a1:int,a2:int,res:real),
  |a1-a2| <= k =>
   exp( (-(|a1%r-res|) + |a2%r-res|)/(k%r/eps)) <= exp(eps).
unset lap_lem_aux3, lap_lem_aux4.
lemma lap_lem_aux8 : forall (a1:int,a2:int,res:real),
  |a1-a2| <= k =>
   exp( (-(|a1%r-res|)/(k%r/eps)))* exp((|a2%r-res|)/(k%r/eps)) <= exp(eps).
unset lap_lem_aux6.
lemma lap_lem_aux9 : forall (a1:int,a2:int,res:real),
  |a1-a2| <= k =>
   exp((-(|a1%r-res|)/(k%r/eps)))/ exp(-((|a2%r-res|)/(k%r/eps))) <= exp(eps).
unset lap_lem_aux8.
lemma lap_lem_aux10 : forall (a1:int,a2:int,res:real),
  exp((-(|a1%r-res|)/(k%r/eps)))/ exp(-(|a2%r-res|)/(k%r/eps)) =
  exp((-(|a1%r-res|)/(k%r/eps)))/ exp(-((|a2%r-res|)/(k%r/eps))).

op lap_op (l:real,a:int,k:int,eps:real) = exp(-(|a%r-l|)/(k%r/eps)).

lemma lap_lem_aux12 : forall (a1:int,a2:int,res:real),
  |a1-a2| <= k =>
  lap_op(res,a1,k,eps)/lap_op(res,a2,k,eps)<= exp(eps).
unset lap_lem_aux10.
lemma lap_lem_aux14 : forall (x:real), !(0%r=x) => x*(1%r/x) = 1%r.
lemma lap_lem_aux15 : forall (A,B,C:real),
   0%r<C =>( (A <= B*C) <=> (A*(1%r/C) <= B*C*(1%r/C))).
lemma lap_lem_aux16 : forall (A,B,C:real),
   0%r<C =>( (A <= B*C) <=> (A*(1%r/C) <= B*(C*(1%r/C)))).
lemma lap_lem_aux17 : forall (A,B,C:real),
   0%r<C =>( (A <= B*C) <=> ((A*(1%r/C)) <= (B*1%r))).
lemma lap_lem_aux18 : forall (a1:int,a2:int,res:real),
  lap_op(res,a1,k,eps)/lap_op(res,a2,k,eps)<= exp(eps)
  =>
  lap_op(res,a1,k,eps)<= exp(eps)*lap_op(res,a2,k,eps) .
timeout 60.
lemma lap_lem : forall (a1:int,a2:int,res:real),
  |a1-a2| <= k =>
  lap_op(res,a1,k,eps) <= exp(eps)*lap_op(res,a2,k,eps).

(* pop lap : (int, int, real) -> real. *)
(* pop lap (a:int,k:int,eps:real) = (z:real) -> exp(-(|a%r-z|) / (k%r/eps) ). *)
pop lap (a:int,k:int,eps:real) = (z:real) -> lap_op(z,a,k,eps).

lemma lap_spec(v1:int,v2:int) :
  x1=lap(v1,k,eps) ~ x2=lap(v2,k,eps):
  (|v1-v2|)<=k ==[exp(eps);0%r]==> x1=x2.

(* pop lap' : (int, int, real) -> real. *)

(* axiom lap_spec'(v1:int,k:int,eps:real,v2:int) : *)
(*   x1=lap(v1,k,eps) ~ x2=lap(v2,k,eps): *)
(*   (v1-v2<=k && v2-v1<=k) ==[exp(eps);0%r]==> x1=x2. *)



(* pop_axiom spec_name(params) : *)
(*   x1=pop_name(args1) ~ x2=pop_name(args2) : *)
(*   pre ==[alpha;delta]==> x1=x2. *)

(* pop_lemma spec_name(params) : *)
(*   x1=pop_name(args1) ~ x2=pop_name(args2) : *)
(*   pre ==[alpha;delta]==> x1=x2. *)
  
(* forall (params), pre => pop_weight(args1) <= alpha* pop_weight(args2)+delta. *)


  
