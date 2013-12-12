theory T.
  type t.

  op Z   : t.
  op add : t -> t -> t.

  axiom L1 : forall x, add x Z = x.
  axiom L2 : forall x, add x Z = x.

  theory U.
    axiom L3 : forall x, add x Z = x.
  end U.
end T.

clone T as U proof U.* by admit, *.

realize L1. proof -strict. admit. qed.
realize L2. proof -strict. admit. qed.
