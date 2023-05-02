(*TODO: if the unicity of finite fields of the same cardinal up to isomorphism is needed.*)

(*
In PolyFiniteField:
- create a new abstract theory with a relevant name
- clone SubFiniteField to get two finite fields A and B, A being a subfield of B.
- clone PolyFiniteField for both A end B
- clone SubIDomain to show that polynomials over A are a sub integral domain of the polynomials over B
- clone the relevant theory about Ideals using the inbtegral domain of polynomials over A
- define the minimal polynomial of an element b of B as the generator of the ideal of the polynomials over A formed by the polynomials over A having b as a root
- show that the minimal polynomial is irreducible (that's because A is an integral domain)
- show that the minimal polynomial divides X^(card B) - X
- show that the degree of the minimal polynomial of a generator g of of the unitaries of B is exactly n (+1 because of the peculiar way the degree is defined)
  this requires showing that 1, g, g^2, ..., g^(n -1) is a basis by a cardinality argument, and using the minimality
  this should be the actual hard part, but everything regarding the cardinality should be available

In this file:
- create a new abstract theory with the relevant name
- clone two instances of FiniteField, to represent two fields A and B
- add an axiom saying that they have the same cardinal
- prove the lemma saying they have the same characteristic
- clone FiniteField_ZModP twice to get the fact that they are both superfield of some ZModP
- clone the previously mentionned theory in PolyFiniteField twice with the two fields being the ZModP and A for the first, B for the second
- take a generator g of A, it's minimal polynomial P, and take a root of P in B called h
- construct the isomorphism by mapping g to h, and and thus 0 to 0 and any power of g to the same power of h
- show that it actually is an isomorphism: this should be the other hard part
*)
