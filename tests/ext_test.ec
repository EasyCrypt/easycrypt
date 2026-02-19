require import AllCore Int List.

print List.Iota.iota_.
print List.all.
print List.Iota.

lemma random : List.all (fun i => i = i)
    (List.Iota.iota_ 0 10).
    proof.

      extens trivial.
    qed.
    
