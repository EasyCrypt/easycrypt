require import AllCore Bool IntDiv CoreMap List Distr QFABV.
from Jasmin require import JModel JArray.

clone import PolyArray as Array2 with op size <- 2.

bind array Array2."_.[_]" Array2."_.[_<-_]" Array2.to_list Array2.of_list Array2.t 2.
realize tolistP by admit.
realize eqP by admit.
realize get_setP by admit.
realize get_out by admit.

export Array2.

(* ----------- BEGIN BOOL BINDINGS ---------- *)
op bool2bits (b : bool) : bool list = [b].
op bits2bool (b: bool list) : bool = List.nth false b 0.

op i2b (i : int) = (i %% 2 <> 0).
op b2si (b: bool) = 0.

bind bitstring bool2bits bits2bool b2i b2si i2b bool 1.
realize size_tolist by auto.
realize tolistP by auto.
realize oflistP by admit.
realize ofintP by admit.
realize touintP by admit.
realize tosintP by auto.
      
bind op bool (&&) "mul".
realize bvmulP by admit.

bind op bool (^^) "add".
realize bvaddP by admit.

op sub (a : bool, b: bool) : bool = 
  a ^^ b.

bind op bool sub "sub".
realize bvsubP by admit.

(* bind op bool udiv "udiv".
   realize bvudivP by admit.  

bind op bool umod "urem".
realize bvuremP by admit. *)

bind op bool (/\) "and".
realize bvandP by admit.

bind op bool (\/) "or".
realize bvorP by admit.

bind op bool [!] "not".
realize bvnotP by admit.

(* TODO: Add shifts once we have truncate/extend *)


(* ----------- BEGIN W8 BINDINGS ---------- *)
bind bitstring W8.w2bits W8.bits2w W8.to_uint W8.to_sint W8.of_int W8.t 8.
realize size_tolist by auto.
realize tolistP by auto.
realize oflistP by admit.
realize ofintP by admit.
realize touintP by admit.
realize tosintP by admit.

bind op W8.t W8.( + ) "add".
realize bvaddP by admit.

bind op W8.t W8.( * ) "mul".
realize bvmulP by admit.

op W8_sub (a : W8.t, b: W8.t) : W8.t = 
  a - b.

bind op W8.t W8_sub "sub".
realize bvsubP by admit.

bind op W8.t W8.\udiv "udiv".
realize bvudivP by admit.

bind op W8.t W8.\umod "urem".
realize bvuremP by admit.

bind op W8.t W8.andw "and".
realize bvandP by admit.

bind op W8.t W8.orw "or".
realize bvorP by admit.

bind op W8.t W8.(+^) "xor".
realize bvxorP by admit.

bind op W8.t W8.invw "not".
realize bvnotP by admit.

bind op [bool & W8.t] W8.\ult "ult".
realize bvultP by admit.

bind op [bool & W8.t] W8.\ule "ule".
realize bvuleP by admit.

bind op [bool & W8.t] W8.\slt "slt".
realize bvsltP by admit.

bind op [bool & W8.t] W8.\sle "sle".
realize bvsleP by admit.

bind op W8.t W8.(`>>`) "shr".
realize bvshrP by admit. 

bind op W8.t W8.(`<<`) "shl".
realize bvshlP by admit.

bind op W8.t W8.(`|>>`) "ashr".
realize bvashrP by admit.



(* ----------- BEGIN W16 BINDINGS ---------- *)

bind bitstring W16.w2bits W16.bits2w W16.to_uint W16.to_sint W16.of_int W16.t 16.
realize size_tolist by auto.
realize tolistP by auto.
realize oflistP by admit.
realize ofintP by admit.
realize touintP by admit.
realize tosintP by admit.

bind op W16.t W16.( + ) "add".
realize bvaddP by admit.

bind op W16.t W16.( * ) "mul".
realize bvmulP by admit.

op W16_sub (a : W16.t, b: W16.t) : W16.t = 
  a - b.

bind op W16.t W16_sub "sub".
realize bvsubP by admit.

bind op W16.t W16.\udiv "udiv".
realize bvudivP by admit.

bind op W16.t W16.\umod "urem".
realize bvuremP by admit.

bind op W16.t W16.andw "and".
realize bvandP by admit.

bind op W16.t W16.orw "or".
realize bvorP by admit.

bind op W16.t W16.(+^) "xor".
realize bvxorP by admit.

bind op W16.t W16.invw "not".
realize bvnotP by admit.

bind op [bool & W16.t] W16.\ult "ult".
realize bvultP by admit.

bind op [bool & W16.t] W16.\ule "ule".
realize bvuleP by admit.

bind op [bool & W16.t] W16.\sle "sle".
realize bvsleP by admit.

bind op [bool & W16.t] W16.\slt "slt".
realize bvsltP by admit.

op uext8_16 (w: W8.t) : W16.t = 
  W16.of_int (W8.to_uint w).

bind op [W8.t & W16.t] uext8_16 "zextend".
realize bvzextendP by admit.

op sext8_16 (w: W8.t) : W16.t = 
  W16.of_int (W8.to_sint w).

bind op [W8.t & W16.t] sext8_16 "sextend".
realize bvsextendP by admit.

op concat8_8_16 (w: W8.t) (w: W8.t) : W16.t.

bind op [W8.t & W8.t & W16.t] concat8_8_16 "concat".
realize bvconcatP by admit.


op shl16 (w: W16.t) (sa: W16.t) : W16.t.

lemma shl_shift w sa : 
    W16.(`<<`) w sa = shl16 w (uext8_16 sa) by admit.

bind op W16.t shl16 "shl".
realize bvshlP by admit.

(* TODO: Add shifts once we have truncate/extend *)


(* ----------- BEGIN W32 BINDINGS ---------- *)
bind bitstring W32.w2bits W32.bits2w W32.to_uint W32.to_sint W32.of_int W32.t 32.
realize size_tolist by auto.
realize tolistP by auto.
realize oflistP by admit.
realize touintP by admit.
realize tosintP by admit.
realize ofintP by admit.

bind op W32.t W32.( + ) "add".
realize bvaddP by admit.

bind op W32.t W32.( * ) "mul".
realize bvmulP by admit.

op W32_sub (a : W32.t, b: W32.t) : W32.t = 
  a - b.

bind op W32.t W32_sub "sub".
realize bvsubP by admit.

bind op W32.t W32.\udiv "udiv".
realize bvudivP by admit.

bind op W32.t W32.\umod "urem".
realize bvuremP by admit.

bind op W32.t W32.andw "and".
realize bvandP by admit.

bind op W32.t W32.orw "or".
realize bvorP by admit.

bind op W32.t W32.(+^) "xor".
realize bvxorP by admit.   

bind op W32.t W32.invw "not".
realize bvnotP by admit.

bind op [W32.t & bool] W32."_.[_]" "get".
realize bvgetP by admit.

(* TODO: Add shifts once we have truncate/extend *)


(* ----------- BEGIN W64 BINDINGS ---------- *)

bind bitstring W64.w2bits W64.bits2w W64.to_uint W64.to_sint W64.of_int W64.t 64.
realize size_tolist by auto.
realize tolistP by auto.
realize oflistP by admit.
realize touintP by admit.
realize tosintP by admit.
realize ofintP by admit.

bind op W64.t W64.( + ) "add".
realize bvaddP by admit.

bind op W64.t W64.( * ) "mul".
realize bvmulP by admit.

op W64_sub (a : W64.t, b: W64.t) : W64.t = 
  a - b.

bind op W64.t W64_sub "sub".
realize bvsubP by admit.

bind op W64.t W64.\udiv "udiv".
realize bvudivP by admit.

bind op W64.t W64.\umod "urem".
realize bvuremP by admit.

bind op W64.t W64.andw "and".
realize bvandP by admit.

bind op W64.t W64.orw "or".
realize bvorP by admit.

bind op W64.t W64.(+^) "xor".
realize bvxorP by admit.

bind op W64.t W64.invw "not".
realize bvnotP by admit.

(* TODO: Add shifts once we have truncate/extend *)


(* ----------- BEGIN W128 BINDINGS ---------- *)

bind bitstring W128.w2bits W128.bits2w W128.to_uint W128.to_sint W128.of_int W128.t 128.
realize size_tolist by auto.
realize tolistP by auto.
realize oflistP by admit.
realize touintP by admit.
realize tosintP by admit.
realize ofintP by admit.

bind op W128.t W128.( + ) "add".
realize bvaddP by admit.

bind op W128.t W128.( * ) "mul".
realize bvmulP by admit.

op W128_sub (a : W128.t, b: W128.t) : W128.t = 
  a - b.

bind op W128.t W128_sub "sub".
realize bvsubP by admit.

bind op W128.t W128.\udiv "udiv".
realize bvudivP by admit.

bind op W128.t W128.\umod "urem".
realize bvuremP by admit.

bind op W128.t W128.andw "and".
realize bvandP by admit.

bind op W128.t W128.orw "or".
realize bvorP by admit.

bind op W128.t W128.(+^) "xor".
realize bvxorP by admit.

bind op W128.t W128.invw "not".
realize bvnotP by admit.

(* TODO: Add shifts once we have truncate/extend *)

(* ----------- BEGIN W256 BINDINGS ---------- *)

bind bitstring W256.w2bits W256.bits2w W256.to_uint W256.to_sint W256.of_int W256.t 256.
realize size_tolist by auto.
realize tolistP by auto.
realize oflistP by admit.
realize touintP by admit.
realize tosintP by admit.
realize ofintP by admit.

bind op W256.t W256.( + ) "add".
realize bvaddP by admit.

bind op W256.t W256.( * ) "mul".
realize bvmulP by admit.

op W256_sub (a : W256.t, b: W256.t) : W256.t = 
  a - b.

bind op W256.t W256_sub "sub".
realize bvsubP by admit.

bind op W256.t W256.\udiv "udiv".
realize bvudivP by admit.

bind op W256.t W256.\umod "urem".
realize bvuremP by admit.

bind op W256.t W256.andw "and".
realize bvandP by admit.

bind op W256.t W256.orw "or".
realize bvorP by admit.

bind op W256.t W256.(+^) "xor".
realize bvxorP by admit.

bind op W256.t W256.invw "not".
realize bvnotP by admit.

(* TODO: Add shifts once we have truncate/extend *)

(* ----------- BEGIN SPEC FILE BINDINDS ---------- *)


(*bind circuit W32.(`<<`) "LSHIFT32".
bind circuit W32.(`>>`) "RSHIFTL_32".
bind circuit CoreInt.lt "LT_256".
*)
(* -- AVX2 VECTORIZED -- *)
(* FIXME: Check new types
bind circuit VPSUB_16u16 "VPSUB_16u16".
bind circuit VPSRA_16u16 "VPSRA_16u16".
bind circuit VPADD_16u16 "VPADD_16u16".
bind circuit VPBROADCAST_16u16 "VPBROADCAST_16u16".
bind circuit VPMULH_16u16 "VPMULH_16u16".
bind circuit VPMULL_16u16 "VPMULL_16u16".
bind circuit VPMULHRS_16u16 "VPMULHRS_16u16".
bind circuit VPACKUS_16u16 "VPACKUS_16u16".
bind circuit VPMADDUBSW_256 "VPMADDUBSW_256".
bind circuit VPERMD "VPERMD".
*)


bind op [bool & W16.t] W16.init "init".
realize bvinitP by admit.

bind op [bool & W32.t] W32.init "init".
realize bvinitP by admit.

op map_test (f: W16.t -> W16.t) (arr: W16.t Array2.t) : W16.t Array2.t =
  Array2.map f arr.

bind op [W16.t & W16.t & Array2.t] map_test "map".
realize mapP by admit.
