require import Real Int.

module M = {
  var b: bool

  proc run() = {
    M.b <- false;
  }
}.

lemma dep_bound : phoare[M.run : M.b ==> !M.b] = (b2i M.b)%r.
proof. by proc; auto => &hr ->. qed.

equiv triv_equiv : M.run ~ M.run : true ==> ={M.b}.
proof. proc; auto. qed.

lemma bad_bound : phoare[M.run : true ==> !M.b] = (b2i M.b)%r.
proof.
conseq triv_equiv dep_bound => //=.
move => &1.
fail smt().
abort.

lemma dep_bound_conseq : 
  phoare[M.run : !M.b ==> !M.b] = (1-b2i M.b)%r.
proof.
conseq triv_equiv dep_bound => //=.
move => &1 -> /=.
by exists true => />.
qed.

lemma nodep_bound : phoare[M.run: true ==> true] = 1%r.
proof. proc; auto. qed.

lemma nodep_bound_conseq :
  phoare[M.run : !M.b ==> !M.b] = 1%r.
proof.
conseq triv_equiv dep_bound => //=.
move => &1 /> _.
by exists true.
qed.

