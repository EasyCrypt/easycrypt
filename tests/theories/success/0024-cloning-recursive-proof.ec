(* -------------------------------------------------------------------- *)
theory T.
  theory U.
    axiom False : false.
  end U.
end T.

(* -------------------------------------------------------------------- *)
clone T as T' proof *.

realize U.False. proof. admit. qed.

(* -------------------------------------------------------------------- *)
clone T as T'' proof *, U.* by admit.

lemma L1 : false by apply T''.U.False.

