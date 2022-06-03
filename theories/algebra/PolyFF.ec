require import AllCore List Ring Int IntDiv FiniteField Poly Ideal.


abstract theory PolyFF.
   
  clone import FiniteField as FF.

  (*TODO*)
  print Poly.Poly.
  (*clone include Poly.Poly with theory IDCoeff <- FF.*)

  (*TODO: some stuff about irreducible polynomials should be added in Poly.Poly directly.*)
  (*TODO: prove that there are infinitely many irreducible polynomials of arbitrairly large degree.*)

end PolyFF.


abstract theory FFQuotient.

  (*TODO: I should be able to find this, and then clone include it and link it to Polynomials and irreducible polynomials, and show that this is a field.*)
  print RingQuotient.

end FFQuotient.
