(*open Pretty*)
 

type code = 
  | Citem    of string * int * (int * int)
  | Cblock   of code list
  | Cseq     of code list
  | Ciseq    of code list
  | Ccascade of code * code
  | Cpack    of code list
  | Cinstr   of code list
  | Cipack   of code list
(*  | Cgroup   of code*)
  | Cnewline
  | Cbreak

let citem x    = 
  Citem (x,0,(0,0))
	
