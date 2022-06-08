require import AllCore List Ring Int IntDiv Characteristic Finite ZModP.
require FinType.


abstract theory FiniteField.

  clone include Field.

  clone import FinType.FinType with type t <= t.

  op in_subfield d x = exp x d = x.

  lemma in_subfield_0 d : in_subfield d zeror.
  proof.
    admit.
  qed.

  lemma in_subfield_1 d : in_subfield d oner.
  proof.
    admit.
  qed.

  lemma in_subfield_card x : in_subfield card x.
  proof.
    admit.
  qed.

  lemma in_subfield_dvd m n x : 1 < m => m %| n => in_subfield m x => in_subfield n x.
  proof.
    admit.
  qed.

  lemma in_subfield_add d x y : in_subfield d x => in_subfield d y => in_subfield d (x + y).
  proof.
    admit.
  qed.

  lemma in_subfield_mul d x y : in_subfield d x => in_subfield d y => in_subfield d (x * y).
  proof.
    admit.
  qed.

end FiniteField.


abstract theory FiniteField_Characteristic.

  clone import FiniteField as FF.

  clone include Field_Characteristic with theory F <- FF.

  lemma prime_char : prime char.
  proof.
    admit.
  qed.

  clone import ZModField as Fp with
    op p <- char,
    axiom prime_p <- prime_char.
  (*TODO: why so much stuff in ZModP? No abstract theory for Z/pZ?*)
  (*proof *.*)

end FiniteField_Characteristic.


abstract theory ZModField_Finite.

  clone include FiniteField.

  (*TODO*)
  (*clone include ZModField.*)

end ZModField_Finite.
