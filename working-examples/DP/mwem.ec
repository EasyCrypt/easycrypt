
type key.
type val.
type query.
cnst dummy_query: query.

type database=(key,val) map.

pred diff1 (d1: database, d2: database) = 
  exists (k:key), forall (k':key), k<>k' => d1[k']=d2[k'].

cnst dummy_db: database.

pop uniform_db: () -> database.

op eval: (query,database)->real.


(* op exp: real -> real. *)

axiom  exp_pow : forall (eps:real,x:real),  exp (eps / x) ^ x = exp (eps).

pop lap: (real,real) -> real.

axiom lap_spec(k:real,v1:real,v2:real,eps:real) :
  x1=lap(v1,eps/k) ~ x2=lap(v2,eps/k):
  (v1-v2<=k && v2-v1<=k) ==[exp(eps);0%r]==> x1=x2.




pop expM : (database, database, real) -> query.



pred sens_score (k:real,d1:database,d2:database) = 
    forall (q:query), eval(q,d1) - eval(q,d2)<= k && eval(q,d2) - eval(q,d1)<= k.



axiom expM_spec (dt1, dt2, d1, d2:database, eps:real, k:real):
  q1=expM(dt1,d1,eps) ~ q2= expM(dt2,d2,eps):
  d1=d2 && sens_score(k,dt1,dt2) ==[exp(2%r*k*eps);0%r]==> q1=q2.
 
(* next axiom should follow from the fact that queries return results in [-1,1]
and are linear *)

axiom diff1_score: 
  forall (d1:database, d2:database, q: query), diff1(d1,d2) => sens_score(2%r,d1,d2).



(* Every query returns a value between -1 and 1 *)


pop update_db: (database,real,query)->database.


cnst N: int.
axiom N_pos : 1 <= N.
cnst eps: real.


game MWEM ={
  var Dt: database

  fun pick_query (D: database): query ={
    var q:query = dummy_query;
    q = expM(Dt,D,eps/ (2%r * N%r));
    return q;
  }


  fun Main () : database ={
    var S: database;
    var i: int = 0;
    var q: query = dummy_query;
    var m:real= 0%r;

    S=uniform_db();
    
    while (i< N) {
      q=pick_query(S);
      m=lap(eval(q,Dt),eps/ (2%r * N%r));
      S=update_db(S,m,q);
      i= i+1;
    }
    return S;
  } 

}.


axiom exp_pos : forall (x:real), 0%r < exp (x).

timeout 10.
equiv mwemDP: MWEM.Main ~ MWEM.Main :
diff1(Dt{1},Dt{2}) ==[exp(eps);0%r]==>={res}.
while (exp(eps/ N%r)), 0%r, i{1}, 0, N : diff1(Dt{1},Dt{2}) && ={S,i}; [trivial| ].
wp; rnd.
apply: lap_spec(2%r*N%r,eval(q,Dt){1},eval(q,Dt){2},eps).
inline.
wp.
apply: expM_spec(Dt{1},Dt{2},D{1},D{2},eps/ (2%r * N%r),2%r).
trivial.
save.
