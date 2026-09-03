(* Regression test for issue #1046.

   When a datatype's type is overridden during cloning, an operator whose
   body pattern-matches on the datatype's constructors (i.e. compiles to
   `OP_Fix`) used to crash with `anomaly: EcTheoryReplay.CoreIncompatible`.
   The replay machinery redirects the source datatype's constructors to the
   target datatype's constructors only through operator definitions
   (`Fop`/`Eop` expression nodes), so the constructor *paths* stored in
   `OP_Fix` match branches were left pointing at the source datatype and the
   operator-compatibility check saw unequal constructor paths.

   Both override modes must accept these clones. *)

require import Int.

theory Thy.
  type ATy = [ CA | CB of int ].

  op getit (x : ATy) =
    with x = CA   => 0
    with x = CB n => n.

  op mk = CB 3.
end Thy.

clone Thy as Thy1.

(* plain alias override *)
clone Thy as Thy2 with
  type ATy = Thy1.ATy,
  op getit <= Thy1.getit,
  op mk    <= Thy1.mk.

(* inline override *)
clone Thy as Thy3 with
  type ATy <- Thy1.ATy,
  op getit <= Thy1.getit,
  op mk    <= Thy1.mk.

(* No operator override: the replayed match operator must have its branch
   constructors redirected to the target datatype, so it reduces on the
   target's constructor applications. *)
clone Thy as Thy4 with
  type ATy = Thy1.ATy.

lemma getit4 : Thy4.getit (Thy1.CB 5) = 5.
proof. done. qed.

(* Recursive match operator: exercises the recursive occurrence
   (opf_recp) together with the constructor redirect. Only the inline
   override is checked here: aliasing the type of a *recursive* datatype
   is rejected by the type-compatibility check for an unrelated reason
   (the constructor argument that mentions the datatype itself is not
   redirected), independently of this fix. *)
theory RThy.
  type RTy = [ RNil | RCons of int & RTy ].

  op total (x : RTy) =
    with x = RNil       => 0
    with x = RCons n xs => n + total xs.
end RThy.

clone RThy as RThy1.

clone RThy as RThy2 with
  type RTy <- RThy1.RTy,
  op total <= RThy1.total.
