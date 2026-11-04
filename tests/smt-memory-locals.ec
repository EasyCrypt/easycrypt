(* smt on goals mentioning program variables: locals, arg, globals, Pr *)
require import AllCore Distr DBool.

module G = { var g : int }.

module M = {
  proc f (x y : int) : int = {
    var z : int;
    z <- x + y;
    G.g <- z;
    return z + 1;
  }
  proc one (x : int) : int = { return x + 1; }
  proc r () : bool = { var b; b <$ {0,1}; return b; }
}.

(* a local in a hoare post *)
lemma f_hoare : hoare [M.f : 0 <= x /\ 0 <= y ==> 1 <= res /\ 0 <= G.g].
proof. by proc; wp; skip => &hr; smt(). qed.

(* the argument variable *)
lemma f_arg : hoare [M.f : arg = (1, 2) ==> res = 4].
proof. by proc; wp; skip => &hr; smt(). qed.

lemma f_arg2 : hoare [M.f : arg.`1 = 1 /\ y = 2 ==> res = 4].
proof. by proc; wp; skip => &hr; smt(). qed.

(* a single parameter: arg is the parameter *)
lemma one_arg : hoare [M.one : arg = 1 ==> res = 2].
proof. by proc; wp; skip => &hr; smt(). qed.

(* equiv with ={arg} and locals of both sides *)
lemma f_equiv : equiv [M.f ~ M.f : ={arg} ==> ={res, G.g}].
proof. by proc; wp; skip => &1 &2; smt(). qed.

lemma f_equiv2 : equiv [M.f ~ M.f : x{1} = y{2} /\ y{1} = x{2} ==> ={res}].
proof. by proc; wp; skip => &1 &2; smt(). qed.

(* memories in a Pr statement *)
lemma r_pr &m : Pr[M.r() @ &m : res] = 1%r / 2%r.
proof. byphoare => //; proc; rnd; skip => &hr; smt(dbool1E). qed.

lemma r_pr2 &m1 &m2 : Pr[M.r() @ &m1 : res] = Pr[M.r() @ &m2 : res].
proof. by rewrite (r_pr &m1) (r_pr &m2). qed.

lemma r_pr3 &m : G.g{m} = 3 => Pr[M.r() @ &m : res /\ G.g = 3] = 1%r / 2%r.
proof. move=> h; byphoare (_ : G.g = 3 ==> _) => //; proc; rnd; skip => &hr; smt(dbool1E). qed.
