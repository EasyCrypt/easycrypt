require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel.

abbrev pc_permidx_s = W256.of_int 25108406943008224694375472445797499139581786974313141764103.


abbrev pc_shift2_s = W16.of_int 4097.


abbrev pc_mask_s = W16.of_int 15.


abbrev pc_shift1_s = W16.of_int 512.


abbrev jvx16 = W256.of_int 35618413472725370924601624884262448072237272005411583588485930205470676438719.


abbrev jqx16 = W256.of_int 5881923629679188442283784376194736327817742869488325897419002016668082834689.


module M = {
  proc _poly_compress_1 (rp_0:W256.t, rp_1:W256.t, rp_2:W256.t, rp_3:W256.t,
                         a_0:W256.t, a_1:W256.t, a_2:W256.t, a_3:W256.t,
                         a_4:W256.t, a_5:W256.t, a_6:W256.t, a_7:W256.t,
                         a_8:W256.t, a_9:W256.t, a_10:W256.t, a_11:W256.t,
                         a_12:W256.t, a_13:W256.t, a_14:W256.t, a_15:W256.t) : 
  W256.t * W256.t * W256.t * W256.t * W256.t * W256.t * W256.t * W256.t *
  W256.t * W256.t * W256.t * W256.t * W256.t * W256.t * W256.t * W256.t *
  W256.t * W256.t * W256.t * W256.t = {
    
    var qx16:W256.t;
    var r:W256.t;
    var r_0:W256.t;
    var t:W256.t;
    var t_0:W256.t;
    var r_1:W256.t;
    var a_0_0:W256.t;
    var r_2:W256.t;
    var r_3:W256.t;
    var t_1:W256.t;
    var t_2:W256.t;
    var r_4:W256.t;
    var a_1_0:W256.t;
    var r_5:W256.t;
    var r_6:W256.t;
    var t_3:W256.t;
    var t_4:W256.t;
    var r_7:W256.t;
    var a_2_0:W256.t;
    var r_8:W256.t;
    var r_9:W256.t;
    var t_5:W256.t;
    var t_6:W256.t;
    var r_10:W256.t;
    var a_3_0:W256.t;
    var r_11:W256.t;
    var r_12:W256.t;
    var t_7:W256.t;
    var t_8:W256.t;
    var r_13:W256.t;
    var a_4_0:W256.t;
    var r_14:W256.t;
    var r_15:W256.t;
    var t_9:W256.t;
    var t_10:W256.t;
    var r_16:W256.t;
    var a_5_0:W256.t;
    var r_17:W256.t;
    var r_18:W256.t;
    var t_11:W256.t;
    var t_12:W256.t;
    var r_19:W256.t;
    var a_6_0:W256.t;
    var r_20:W256.t;
    var r_21:W256.t;
    var t_13:W256.t;
    var t_14:W256.t;
    var r_22:W256.t;
    var a_7_0:W256.t;
    var r_23:W256.t;
    var r_24:W256.t;
    var t_15:W256.t;
    var t_16:W256.t;
    var r_25:W256.t;
    var a_8_0:W256.t;
    var r_26:W256.t;
    var r_27:W256.t;
    var t_17:W256.t;
    var t_18:W256.t;
    var r_28:W256.t;
    var a_9_0:W256.t;
    var r_29:W256.t;
    var r_30:W256.t;
    var t_19:W256.t;
    var t_20:W256.t;
    var r_31:W256.t;
    var a_10_0:W256.t;
    var r_32:W256.t;
    var r_33:W256.t;
    var t_21:W256.t;
    var t_22:W256.t;
    var r_34:W256.t;
    var a_11_0:W256.t;
    var r_35:W256.t;
    var r_36:W256.t;
    var t_23:W256.t;
    var t_24:W256.t;
    var r_37:W256.t;
    var a_12_0:W256.t;
    var r_38:W256.t;
    var r_39:W256.t;
    var t_25:W256.t;
    var t_26:W256.t;
    var r_40:W256.t;
    var a_13_0:W256.t;
    var r_41:W256.t;
    var r_42:W256.t;
    var t_27:W256.t;
    var t_28:W256.t;
    var r_43:W256.t;
    var a_14_0:W256.t;
    var r_44:W256.t;
    var r_45:W256.t;
    var t_29:W256.t;
    var t_30:W256.t;
    var r_46:W256.t;
    var a_15_0:W256.t;
    var x16p:W256.t;
    var v:W256.t;
    var shift1:W256.t;
    var mask:W256.t;
    var shift2:W256.t;
    var permidx:W256.t;
    var f0:W256.t;
    var f1:W256.t;
    var f2:W256.t;
    var f3:W256.t;
    var f0_0:W256.t;
    var f1_0:W256.t;
    var f2_0:W256.t;
    var f3_0:W256.t;
    var f0_1:W256.t;
    var f1_1:W256.t;
    var f2_1:W256.t;
    var f3_1:W256.t;
    var f0_2:W256.t;
    var f1_2:W256.t;
    var f2_2:W256.t;
    var f3_2:W256.t;
    var f0_3:W256.t;
    var f2_3:W256.t;
    var f0_4:W256.t;
    var f2_4:W256.t;
    var f0_5:W256.t;
    var f0_6:W256.t;
    var rp_0_0:W256.t;
    var f0_7:W256.t;
    var f1_3:W256.t;
    var f2_5:W256.t;
    var f3_3:W256.t;
    var f0_8:W256.t;
    var f1_4:W256.t;
    var f2_6:W256.t;
    var f3_4:W256.t;
    var f0_9:W256.t;
    var f1_5:W256.t;
    var f2_7:W256.t;
    var f3_5:W256.t;
    var f0_10:W256.t;
    var f1_6:W256.t;
    var f2_8:W256.t;
    var f3_6:W256.t;
    var f0_11:W256.t;
    var f2_9:W256.t;
    var f0_12:W256.t;
    var f2_10:W256.t;
    var f0_13:W256.t;
    var f0_14:W256.t;
    var rp_1_0:W256.t;
    var f0_15:W256.t;
    var f1_7:W256.t;
    var f2_11:W256.t;
    var f3_7:W256.t;
    var f0_16:W256.t;
    var f1_8:W256.t;
    var f2_12:W256.t;
    var f3_8:W256.t;
    var f0_17:W256.t;
    var f1_9:W256.t;
    var f2_13:W256.t;
    var f3_9:W256.t;
    var f0_18:W256.t;
    var f1_10:W256.t;
    var f2_14:W256.t;
    var f3_10:W256.t;
    var f0_19:W256.t;
    var f2_15:W256.t;
    var f0_20:W256.t;
    var f2_16:W256.t;
    var f0_21:W256.t;
    var f0_22:W256.t;
    var rp_2_0:W256.t;
    var f0_23:W256.t;
    var f1_11:W256.t;
    var f2_17:W256.t;
    var f3_11:W256.t;
    var f0_24:W256.t;
    var f1_12:W256.t;
    var f2_18:W256.t;
    var f3_12:W256.t;
    var f0_25:W256.t;
    var f1_13:W256.t;
    var f2_19:W256.t;
    var f3_13:W256.t;
    var f0_26:W256.t;
    var f1_14:W256.t;
    var f2_20:W256.t;
    var f3_14:W256.t;
    var f0_27:W256.t;
    var f2_21:W256.t;
    var f0_28:W256.t;
    var f2_22:W256.t;
    var f0_29:W256.t;
    var f0_30:W256.t;
    var rp_3_0:W256.t;
    
    qx16 <- jqx16;
    r <- a_0;
    r_0 <- VPSUB_16u16 r qx16;
    t <- VPSRA_16u16 r_0 (W8.of_int 15);
    t_0 <- VPAND_256 t qx16;
    r_1 <- VPADD_16u16 t_0 r_0;
    a_0_0 <- r_1;
    r_2 <- a_1;
    r_3 <- VPSUB_16u16 r_2 qx16;
    t_1 <- VPSRA_16u16 r_3 (W8.of_int 15);
    t_2 <- VPAND_256 t_1 qx16;
    r_4 <- VPADD_16u16 t_2 r_3;
    a_1_0 <- r_4;
    r_5 <- a_2;
    r_6 <- VPSUB_16u16 r_5 qx16;
    t_3 <- VPSRA_16u16 r_6 (W8.of_int 15);
    t_4 <- VPAND_256 t_3 qx16;
    r_7 <- VPADD_16u16 t_4 r_6;
    a_2_0 <- r_7;
    r_8 <- a_3;
    r_9 <- VPSUB_16u16 r_8 qx16;
    t_5 <- VPSRA_16u16 r_9 (W8.of_int 15);
    t_6 <- VPAND_256 t_5 qx16;
    r_10 <- VPADD_16u16 t_6 r_9;
    a_3_0 <- r_10;
    r_11 <- a_4;
    r_12 <- VPSUB_16u16 r_11 qx16;
    t_7 <- VPSRA_16u16 r_12 (W8.of_int 15);
    t_8 <- VPAND_256 t_7 qx16;
    r_13 <- VPADD_16u16 t_8 r_12;
    a_4_0 <- r_13;
    r_14 <- a_5;
    r_15 <- VPSUB_16u16 r_14 qx16;
    t_9 <- VPSRA_16u16 r_15 (W8.of_int 15);
    t_10 <- VPAND_256 t_9 qx16;
    r_16 <- VPADD_16u16 t_10 r_15;
    a_5_0 <- r_16;
    r_17 <- a_6;
    r_18 <- VPSUB_16u16 r_17 qx16;
    t_11 <- VPSRA_16u16 r_18 (W8.of_int 15);
    t_12 <- VPAND_256 t_11 qx16;
    r_19 <- VPADD_16u16 t_12 r_18;
    a_6_0 <- r_19;
    r_20 <- a_7;
    r_21 <- VPSUB_16u16 r_20 qx16;
    t_13 <- VPSRA_16u16 r_21 (W8.of_int 15);
    t_14 <- VPAND_256 t_13 qx16;
    r_22 <- VPADD_16u16 t_14 r_21;
    a_7_0 <- r_22;
    r_23 <- a_8;
    r_24 <- VPSUB_16u16 r_23 qx16;
    t_15 <- VPSRA_16u16 r_24 (W8.of_int 15);
    t_16 <- VPAND_256 t_15 qx16;
    r_25 <- VPADD_16u16 t_16 r_24;
    a_8_0 <- r_25;
    r_26 <- a_9;
    r_27 <- VPSUB_16u16 r_26 qx16;
    t_17 <- VPSRA_16u16 r_27 (W8.of_int 15);
    t_18 <- VPAND_256 t_17 qx16;
    r_28 <- VPADD_16u16 t_18 r_27;
    a_9_0 <- r_28;
    r_29 <- a_10;
    r_30 <- VPSUB_16u16 r_29 qx16;
    t_19 <- VPSRA_16u16 r_30 (W8.of_int 15);
    t_20 <- VPAND_256 t_19 qx16;
    r_31 <- VPADD_16u16 t_20 r_30;
    a_10_0 <- r_31;
    r_32 <- a_11;
    r_33 <- VPSUB_16u16 r_32 qx16;
    t_21 <- VPSRA_16u16 r_33 (W8.of_int 15);
    t_22 <- VPAND_256 t_21 qx16;
    r_34 <- VPADD_16u16 t_22 r_33;
    a_11_0 <- r_34;
    r_35 <- a_12;
    r_36 <- VPSUB_16u16 r_35 qx16;
    t_23 <- VPSRA_16u16 r_36 (W8.of_int 15);
    t_24 <- VPAND_256 t_23 qx16;
    r_37 <- VPADD_16u16 t_24 r_36;
    a_12_0 <- r_37;
    r_38 <- a_13;
    r_39 <- VPSUB_16u16 r_38 qx16;
    t_25 <- VPSRA_16u16 r_39 (W8.of_int 15);
    t_26 <- VPAND_256 t_25 qx16;
    r_40 <- VPADD_16u16 t_26 r_39;
    a_13_0 <- r_40;
    r_41 <- a_14;
    r_42 <- VPSUB_16u16 r_41 qx16;
    t_27 <- VPSRA_16u16 r_42 (W8.of_int 15);
    t_28 <- VPAND_256 t_27 qx16;
    r_43 <- VPADD_16u16 t_28 r_42;
    a_14_0 <- r_43;
    r_44 <- a_15;
    r_45 <- VPSUB_16u16 r_44 qx16;
    t_29 <- VPSRA_16u16 r_45 (W8.of_int 15);
    t_30 <- VPAND_256 t_29 qx16;
    r_46 <- VPADD_16u16 t_30 r_45;
    a_15_0 <- r_46;
    x16p <- jvx16;
    v <- x16p;
    shift1 <- VPBROADCAST_16u16 pc_shift1_s;
    mask <- VPBROADCAST_16u16 pc_mask_s;
    shift2 <- VPBROADCAST_16u16 pc_shift2_s;
    permidx <- pc_permidx_s;
    f0 <- a_0_0;
    f1 <- a_1_0;
    f2 <- a_2_0;
    f3 <- a_3_0;
    f0_0 <- VPMULH_16u16 f0 v;
    f1_0 <- VPMULH_16u16 f1 v;
    f2_0 <- VPMULH_16u16 f2 v;
    f3_0 <- VPMULH_16u16 f3 v;
    f0_1 <- VPMULHRS_16u16 f0_0 shift1;
    f1_1 <- VPMULHRS_16u16 f1_0 shift1;
    f2_1 <- VPMULHRS_16u16 f2_0 shift1;
    f3_1 <- VPMULHRS_16u16 f3_0 shift1;
    f0_2 <- VPAND_256 f0_1 mask;
    f1_2 <- VPAND_256 f1_1 mask;
    f2_2 <- VPAND_256 f2_1 mask;
    f3_2 <- VPAND_256 f3_1 mask;
    f0_3 <- VPACKUS_16u16 f0_2 f1_2;
    f2_3 <- VPACKUS_16u16 f2_2 f3_2;
    f0_4 <- VPMADDUBSW_256 f0_3 shift2;
    f2_4 <- VPMADDUBSW_256 f2_3 shift2;
    f0_5 <- VPACKUS_16u16 f0_4 f2_4;
    f0_6 <- VPERMD permidx f0_5;
    rp_0_0 <- f0_6;
    f0_7 <- a_4_0;
    f1_3 <- a_5_0;
    f2_5 <- a_6_0;
    f3_3 <- a_7_0;
    f0_8 <- VPMULH_16u16 f0_7 v;
    f1_4 <- VPMULH_16u16 f1_3 v;
    f2_6 <- VPMULH_16u16 f2_5 v;
    f3_4 <- VPMULH_16u16 f3_3 v;
    f0_9 <- VPMULHRS_16u16 f0_8 shift1;
    f1_5 <- VPMULHRS_16u16 f1_4 shift1;
    f2_7 <- VPMULHRS_16u16 f2_6 shift1;
    f3_5 <- VPMULHRS_16u16 f3_4 shift1;
    f0_10 <- VPAND_256 f0_9 mask;
    f1_6 <- VPAND_256 f1_5 mask;
    f2_8 <- VPAND_256 f2_7 mask;
    f3_6 <- VPAND_256 f3_5 mask;
    f0_11 <- VPACKUS_16u16 f0_10 f1_6;
    f2_9 <- VPACKUS_16u16 f2_8 f3_6;
    f0_12 <- VPMADDUBSW_256 f0_11 shift2;
    f2_10 <- VPMADDUBSW_256 f2_9 shift2;
    f0_13 <- VPACKUS_16u16 f0_12 f2_10;
    f0_14 <- VPERMD permidx f0_13;
    rp_1_0 <- f0_14;
    f0_15 <- a_8_0;
    f1_7 <- a_9_0;
    f2_11 <- a_10_0;
    f3_7 <- a_11_0;
    f0_16 <- VPMULH_16u16 f0_15 v;
    f1_8 <- VPMULH_16u16 f1_7 v;
    f2_12 <- VPMULH_16u16 f2_11 v;
    f3_8 <- VPMULH_16u16 f3_7 v;
    f0_17 <- VPMULHRS_16u16 f0_16 shift1;
    f1_9 <- VPMULHRS_16u16 f1_8 shift1;
    f2_13 <- VPMULHRS_16u16 f2_12 shift1;
    f3_9 <- VPMULHRS_16u16 f3_8 shift1;
    f0_18 <- VPAND_256 f0_17 mask;
    f1_10 <- VPAND_256 f1_9 mask;
    f2_14 <- VPAND_256 f2_13 mask;
    f3_10 <- VPAND_256 f3_9 mask;
    f0_19 <- VPACKUS_16u16 f0_18 f1_10;
    f2_15 <- VPACKUS_16u16 f2_14 f3_10;
    f0_20 <- VPMADDUBSW_256 f0_19 shift2;
    f2_16 <- VPMADDUBSW_256 f2_15 shift2;
    f0_21 <- VPACKUS_16u16 f0_20 f2_16;
    f0_22 <- VPERMD permidx f0_21;
    rp_2_0 <- f0_22;
    f0_23 <- a_12_0;
    f1_11 <- a_13_0;
    f2_17 <- a_14_0;
    f3_11 <- a_15_0;
    f0_24 <- VPMULH_16u16 f0_23 v;
    f1_12 <- VPMULH_16u16 f1_11 v;
    f2_18 <- VPMULH_16u16 f2_17 v;
    f3_12 <- VPMULH_16u16 f3_11 v;
    f0_25 <- VPMULHRS_16u16 f0_24 shift1;
    f1_13 <- VPMULHRS_16u16 f1_12 shift1;
    f2_19 <- VPMULHRS_16u16 f2_18 shift1;
    f3_13 <- VPMULHRS_16u16 f3_12 shift1;
    f0_26 <- VPAND_256 f0_25 mask;
    f1_14 <- VPAND_256 f1_13 mask;
    f2_20 <- VPAND_256 f2_19 mask;
    f3_14 <- VPAND_256 f3_13 mask;
    f0_27 <- VPACKUS_16u16 f0_26 f1_14;
    f2_21 <- VPACKUS_16u16 f2_20 f3_14;
    f0_28 <- VPMADDUBSW_256 f0_27 shift2;
    f2_22 <- VPMADDUBSW_256 f2_21 shift2;
    f0_29 <- VPACKUS_16u16 f0_28 f2_22;
    f0_30 <- VPERMD permidx f0_29;
    rp_3_0 <- f0_30;
    return (rp_0_0, rp_1_0, rp_2_0, rp_3_0, a_0_0, a_1_0, a_2_0, a_3_0,
    a_4_0, a_5_0, a_6_0, a_7_0, a_8_0, a_9_0, a_10_0, a_11_0, a_12_0, a_13_0,
    a_14_0, a_15_0);
  }
}.

bdep M._poly_compress_1.