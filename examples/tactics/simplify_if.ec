require import AllCore.

module M = {
  proc f (j:int) : int * int = {
    var i, x, y;
    x <- 0;
    y <- 0;
    i <- 0;
    while (i < 6) {
      if (i = j) x <- i;
      else y <- y + i;
      i <- i + 1;
    }
    return (x, y);
  }
}.

hoare fP j_: M.f : j = j_ ==> res = if 0 <= j_ < 6 then (j_, 15 - j_) else (0,15).
proof.
  proc.
  unroll for ^while.
  time wp. (* The size of the condition grow exponentially in the value of the bound (here 6). *)
  skip.
  move => />.
  smt().
qed.

hoare fP_simplify j_: M.f : j = j_ ==> res = if 0 <= j_ < 6 then (j_, 15 - j_) else (0,15).
proof.
  proc.
  unroll for ^while.
  simplify if. (* if instruction are transformed into single assignment *)
  time wp.  (* The size of the wp is now linear in the number of instruction *)
  skip.
  move => />.
  smt().
qed.

hoare fP_simplify2 j_: M.f : j = j_ ==> res = if 0 <= j_ < 6 then (j_, 15 - j_) else (0,15).
proof.
  proc.
  unroll for ^while.
  (* You can select a particular occurence of if using codepos *)
  simplify if ^if. (* Apply the transformation on the first if *)
  simplify if ^if{2}. (* Apply the transformation on the second if *)
  simplify if ^if{-2}. (* Apply the trnasformation of the penultimate if *)
  time wp.
  skip.
  move => />.
  smt().
qed.
