require import AllCore List Ring Int IntDiv FiniteRing Poly Ideal.


abstract theory PolyFF.

  type coeff.
   
  clone import FiniteField as FF with
    type t <= coeff.

  clone include Poly.Poly with
    type coeff <- coeff,
    theory IDCoeff <- FF.F.

end PolyFF.


abstract theory FFQuotient.

  (*TODO: I should be able to find this, and then clone include it and link it to Polynomials and irreducible polynomials, and show that this is a field.*)
  clone import PolyFF as PFF.

  print IdealComRing.
  (*clone include IdealComRing with type t <- poly, theory IComRing <- PolyComRing.*)

  print IdealComRing. print RingQuotient.

end FFQuotient.
