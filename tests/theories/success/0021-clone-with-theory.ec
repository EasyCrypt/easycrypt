theory T.
  type t.

  op Z   : t.
  op add : t -> t -> t.

  axiom L1 : forall x, add x Z = x.
  axiom L2 : forall x, add x Z = x.

  theory U.
    theory I.
      type u.

      op u : u.

      axiom L : forall (x : u), x = u.
    end I.
  end U.
end T.

theory V.
  theory I.
    type u = unit.

    op u = tt.

    lemma L : forall (x : u), x = u by smt.
  end I.
end V.

clone T as W with theory U = V.
