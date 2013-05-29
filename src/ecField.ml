(****** Field Type  ******)
type 'a Field = 
	| Plus of 'a Field list (* (+ [t1,...,tn])  *)
	| Times of 'a Field list
	| Minus of 'a Field  (* (- t)*)
	| Inv of 'a Field  (* inv(t) = 1/t  *)
	| One of 'a 
	| Zero of 'a
	| Value of 'a
(*************************)
