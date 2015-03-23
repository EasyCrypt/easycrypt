(* --------------------------------------------------------------------
 * Copyright (c) - 2012-2015 - IMDEA Software Institute and INRIA
 * Distributed under the terms of the CeCILL-B licence.
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
require import NewIntCore.

(* -------------------------------------------------------------------- *)
import why3 "real" "Real" op "prefix -" as "[-]".

(* -------------------------------------------------------------------- *)
theory Abs.
  import why3 "real" "Abs" op "abs" as "`|_|".
end Abs.

(* -------------------------------------------------------------------- *)
theory FromInt.
  import why3 "real" "FromInt".
end FromInt.

(* -------------------------------------------------------------------- *)
theory PowerInt.
  import why3 "real" "PowerInt" op "power" as "^".
end PowerInt.

(* -------------------------------------------------------------------- *)
theory Square.
  import why3 "real" "Square"   op "sqrt" as "sqrt".
end Square.

(* -------------------------------------------------------------------- *)
export Abs FromInt PowerInt Square.
