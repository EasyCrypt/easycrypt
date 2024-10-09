type symbol = string
module type S =
  sig
    val get_specification : symbol -> Ast.adef option
    val vpermd : Aig.reg -> Aig.reg -> Aig.reg
    val vpermq : Aig.reg -> int -> Aig.reg
    val vpbroadcast_16u16 : Aig.reg -> Aig.reg
    val vpadd_16u16 : Aig.reg -> Aig.reg -> Aig.reg
    val vpadd_32u8 : Aig.reg -> Aig.reg -> Aig.reg
    val vpsub_16u16 : Aig.reg -> Aig.reg -> Aig.reg
    val vpsub_32u8 : Aig.reg -> Aig.reg -> Aig.reg
    val vpand_256 : Aig.reg -> Aig.reg -> Aig.reg
    val vpmaddubsw_256 : Aig.reg -> Aig.reg -> Aig.reg
    val vpmulh_16u16 : Aig.reg -> Aig.reg -> Aig.reg
    val vpmulhrs_16u16 : Aig.reg -> Aig.reg -> Aig.reg
    val vpsra_16u16 : Aig.reg -> int -> Aig.reg
    val vpsrl_16u16 : Aig.reg -> int -> Aig.reg
    val vpsrl_4u64 : Aig.reg -> int -> Aig.reg
    val vpsll_4u64 : Aig.reg -> int -> Aig.reg
    val vpackus_16u16 : Aig.reg -> Aig.reg -> Aig.reg
    val vpackss_16u16 : Aig.reg -> Aig.reg -> Aig.reg
    val vpshufb_256 : Aig.reg -> Aig.reg -> Aig.reg
    val vpcmpgt_16u16 : Aig.reg -> Aig.reg -> Aig.reg
    val vpmovmskb_u256u64 : Aig.reg -> Aig.reg
    val vpunpckl_32u8 : Aig.reg -> Aig.reg -> Aig.reg
    val vpextracti128 : Aig.reg -> int -> Aig.reg
    val vpinserti128 : Aig.reg -> Aig.reg -> int -> Aig.reg
    val vpblend_16u16 : Aig.reg -> Aig.reg -> int -> Aig.reg
    val vpslldq_256 : Aig.reg -> int -> Aig.reg
    val vpsrldq_256 : Aig.reg -> int -> Aig.reg
    val vpslldq_128 : Aig.reg -> int -> Aig.reg
    val vpsrldq_128 : Aig.reg -> int -> Aig.reg
  end
module FromSpec : functor () -> S
