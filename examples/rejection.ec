(* -------------------------------------------------------------------- *)
require import AllCore List.

(* -------------------------------------------------------------------- *)
from Jasmin require import JWord.

(* -------------------------------------------------------------------- *)
type w8   = W8.t.
type w16  = W16.t.
type w32  = W32.t.
type w64  = W64.t.
type w128 = W128.t.
type w256 = W256.t.

(* -------------------------------------------------------------------- *)
op VPERMQ : w256 -> w8 -> w256.
op VPSHUFB_256 : w256 -> w256 -> w256.
op VPSRL_16u16 : w256 -> w8 -> w256.
op VPBLEND_16u16 : w256 -> w256 -> w8 -> w256.
op VPBROADCAST_16u16 : w16 -> w256.
op VPAND_256 : w256 -> w256 -> w256.
op VPCMPGT_16u16 : w256 -> w256 -> w256.
op VPACKSS_16u16 : w256 -> w256 -> w256.
op VPMOVMSKB_u256u64 : w256 -> w64.
op VINSERTI128 : w256 -> w128 -> int -> w256.
op VEXTRACTI128 : w256 -> int -> w128.
op VPADD_32u8 : w256 -> w256 -> w256.
op VPUNPCKL_32u8 : w256 -> w256 -> w256.

(* -------------------------------------------------------------------- *)
op sst : int -> W64.t.

(* -------------------------------------------------------------------- *)
module M = {
  proc gen_matrix_sample_iterate_x3_fast_filter48(
    r0 : w64,
    r1 : w64,
    r2 : w64,
    r3 : w64,
    r4 : w64,
    r5 : w64,
    r6 : w64
  ) = {
    var permq  : w8;            (* VPERMQ  mask *)
    var shfb   : w256;          (* VPSHUFB mask *)
    var andm   : w256;
    var bounds : w256;
    var ones   : w256;

    var f0, f1, g0, g1, g : w256;
    var good : w64;

    var t0_0, t0_1, t1_0, t1_1 : w64;

    var shuffle_0 : w256;
    var shuffle_0_1 : w128;

    var shuffle_1 : w256;
    var shuffle_1_1 : w128;

    var shuffle_t : w256;

    var counter : w64 <- W64.zero;

    permq <- W8.of_int 148; (* FIXME: hex/bin notations *)
    shfb  <- W32u8.pack32 (List.map W8.of_int [
       0;  1;  1;  2;  3;  4;  4;  5;
       6;  7;  7;  8;  9; 10; 10; 11;
       4;  5;  5;  6;  7;  8;  8;  9;
      10; 11; 11; 12; 13; 14; 14; 15
    ]);

    f0 <- VPERMQ (W4u64.pack4 [r0; r1; r2; r3]) permq;
    f1 <- VPERMQ (W4u64.pack4 [r3; r4; r5; r6]) permq;

    f0 <- VPSHUFB_256 f0 shfb;
    f1 <- VPSHUFB_256 f1 shfb;

    g0 <- VPSRL_16u16 f0 (W8.of_int 4);
    g1 <- VPSRL_16u16 f1 (W8.of_int 4);

    f0 <- VPBLEND_16u16 f0 g0 (W8.of_int 170); (* 0xaa *)
    f1 <- VPBLEND_16u16 f1 g1 (W8.of_int 170); (* 0xaa *)

    andm <- VPBROADCAST_16u16 (W16.of_int 4095); (* 0x0fff *)
    f0 <- VPAND_256 f0 andm;
    f1 <- VPAND_256 f1 andm;

    bounds <- VPBROADCAST_16u16 (W16.of_int 3309);
    g0 <- VPCMPGT_16u16 bounds f0;
    g1 <- VPCMPGT_16u16 bounds f1;

    g <- VPACKSS_16u16 g0 g1;
    good <- VPMOVMSKB_u256u64 g;

    t0_0 <- good;
    t0_0 <- t0_0 `&` W64.of_int 255;
    shuffle_0 <- W256.of_int (W64.to_sint (sst (W64.to_uint t0_0)));
    t0_0 <- (POPCNT_64 t0_0).`6;
    counter <- counter + t0_0;

    t0_1 <- good;
    t0_1 <- t0_1 `>>>` 16;
    t0_1 <- t0_1 `&` W64.of_int 255;
    shuffle_0_1 <- W128.of_int (W64.to_sint (sst (W64.to_uint t0_1)));
    t0_1 <- (POPCNT_64 t0_1).`6;
    counter <- counter + t0_1;
    t0_1 <- t0_1 + t0_0;

    t1_0 <- good;
    t1_0 <- t1_0 `>>>` 8;
    t1_0 <- t1_0 `&` W64.of_int 255;
    shuffle_1 <- W256.of_int (W64.to_sint (sst (W64.to_uint t1_0)));
    t1_0 <- (POPCNT_64 t1_0).`6;
    counter <- counter + t1_0;
    t1_0 <- t1_0 + t0_1;

    t1_1 <- good;
    t1_1 <- t1_1 `>>>` 24;
    t1_1 <- t1_1 `&` W64.of_int 255;
    shuffle_1_1 <- W128.of_int (W64.to_sint (sst (W64.to_uint t1_1)));
    t1_1 <- (POPCNT_64 t1_1).`6;
    counter <- counter + t1_1;
    t1_1 <- t1_1 + t1_0;
    
    shuffle_0 <- VINSERTI128 shuffle_0 shuffle_0_1 1;
    shuffle_1 <- VINSERTI128 shuffle_1 shuffle_1_1 1;

    ones <- VPBROADCAST_16u16 (W16.of_int 1);

    shuffle_t <- VPADD_32u8 shuffle_0 ones;
    shuffle_0 <- VPUNPCKL_32u8 shuffle_0 shuffle_t;

    shuffle_t <- VPADD_32u8 shuffle_1 ones;
    shuffle_1 <- VPUNPCKL_32u8 shuffle_1 shuffle_t;

    f0 <- VPSHUFB_256 f0 shuffle_0;
    f1 <- VPSHUFB_256 f1 shuffle_1;

    (*
        matrix.[u128 2*(int) matrix_offset] = (128u)f0;
        matrix.[u128 2*(int) t0_0] = #VEXTRACTI128(f0, 1);
        matrix.[u128 2*(int) t0_1] = (128u)f1;
        matrix.[u128 2*(int) t1_0] = #VEXTRACTI128(f1, 1);
        matrix_offset = t1_1;
      
        return counter, matrix, matrix_offset;
     *)
  }
}.
