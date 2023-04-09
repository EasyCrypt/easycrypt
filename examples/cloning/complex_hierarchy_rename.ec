(*TODO: Pierre-Yves*)

abstract theory T1.
  type t1.
end T1.

abstract theory T2.
  clone include T1.
  type t2.
end T2.

abstract theory S1.
  clone import T1 as T.
  theory S.
    (*The only thing we can put here to allow extending are lemmas.*)
    lemma s1 : true by trivial.
  end S.
end S1.

abstract theory S2.
  clone import T2 as T.
  clone include S1 with
    theory T <- T
    rename [theory] "T" as "Gone"
           [theory] "S" as "S_".
  theory S.
    clone include S_.
    lemma s2 : true by trivial.
  end S.
  (*We should also be able to clear S_ if it contains concrete predicates
    and operators unused elsewhere.*)
  clear [S_.*].
end S2.

(*Also, if we replace all the theories S with abstract theories, we should ba able to clear
  no matter what.*)
