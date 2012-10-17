cnst n : int.

axiom n_pos : 0 <= n.

game Sum = {
  fun Skip() : unit = { }

  fun Loop(): int = {
    var i, sum : int;
    i = 0;
    sum = 0;
    while (i < n) {
      i = i + 1;
      sum = sum + i;
    }
    return sum;
  }
}.

prover "alt-ergo".

equiv test : Sum.Loop ~ Sum.Skip : 0 <= n ==> res{1} = n * (n + 1) / 2.
proof.
 sp; while{1}: (i <= n && sum = i * (i + 1) / 2){1}; trivial.
save.
