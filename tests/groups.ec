type group.
cnst q : int.
cnst g : group.

op [^] : (group, int) -> group as group_pow.
op [*] : (group, group) -> group as group_mul.

axiom group_pow_mod : 
  forall (g1:group, x:int),
    g1^x = g1^(x%q).

axiom group_pow_mult :
  forall (g1:group, x:int, y:int),
    (g1^x)^y = g1^(x*y).

axiom group_pow_com :
  forall (g1:group, x:int, y:int),
    (g1^x)^y = (g1^y)^x.

axiom group_pow_mult_distr :
  forall (g1:group, x:int, y:int),
    g1^x * g1^y = g1^(x+y).

axiom group_mult_com :
  forall (g1,g2:group),
    g1 * g2 = g2 * g1.

axiom group_mult_assoc : 
  forall (g1,g2,g3:group),
    g1 * (g2 * g3) = (g1 * g2) * g3.

axiom plus_mod_idemp_l : 
 forall (a,b,n:int),
   (a + b)%n = ((a%n) + b)%n.

axiom plus_mod_idemp_r : 
 forall (a,b,n:int),
   (a + b)%n = (a + (b%n))%n.

axiom minus_mod_idemp_l : 
 forall (a,b,n:int),
   (a - b)%n = ((a%n) - b)%n.

axiom minus_mod_idemp_r : 
 forall (a,b,n:int),
   (a - b)%n = (a - (b%n))%n.

axiom mod_small : forall (a,n:int),
  (0 <= a  &&  a <= n ) =>
    a%n = a .

game test1 = {
  var pg, z, z1, z2 : int
  fun Main () : group = {
    z1 = [0..q-1];    
    z2 = [0..q-1];
    z = (z1 + pg * z2)%q;
    return g^z;
  }
}.

game test1' = test1 where Main = {
  z = [0..q-1];    
  z2 = [0..q-1];
  z1 = (z - (pg * z2))%q;
  return g^z;
}.

game test = {
  var z,y : int
  fun Main () : int = {
    return z;
  }
}.

game test' = {
  var z, y : int
  fun Main () : int = {
     return z;
  }
}.

equiv _test_test': test.Main ~ test.Main : 
      true ==> ((z * y) = (y * z)){1}.
trivial.
save.

op _inv : int -> int as inv_field.

axiom inv_correct : forall (x:int),
  0 <> x%q =>  (_inv(x) * x)%q = 1.

equiv test_test': test.Main ~ test.Main : (0<>(z%q)){1} ==> 
   ((z * _inv(z))%q = 1){1}.
trivial.
abort.

axiom mod_mult_l : forall (x,y:int),
  (x * y)%q = ((x%q) * y)%q.

axiom mod_mult_r : forall (x,y:int),
  (x * (y%q))%q = (x * y)%q.

axiom inv_correct_2 : forall (x:int, y :int), 
  0 <> x%q =>  ((_inv(x) * x) * y)%q = y%q.

game test2 = {
   var z, z1, z2 : int
   fun Main () : group = {
     z2 = [0..q-1];    
     z = (z1 * z2)%q;
     return g^z;
   }
}.

game test2' = test2 
  where Main = {
    z = [0..q-1];    
    z2 = (_inv(z1) * z)%q;
    return g^z; 
  }.

equiv test2_test2' : test2.Main ~ test2'.Main : 
  ={z1} && (z1%q <> 0){1} ==> ={res,z,z1,z2}.
proof.
 auto.
 rnd ((z1{2}*z)%q), ((_inv(z1{2})*z)%q).
 trivial.
save.
