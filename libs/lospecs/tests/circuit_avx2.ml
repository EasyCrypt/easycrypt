(* ==================================================================== *)
open Lospecs
open Aig

type symbol = string

(* ==================================================================== *)
module type S = sig
  val vpermd : reg -> reg -> reg
  val vpermq : reg -> int -> reg
  val vpbroadcast_16u16 : reg -> reg
  val vpadd_16u16 : reg -> reg -> reg
  val vpadd_32u8 : reg -> reg -> reg
  val vpsub_16u16 : reg -> reg -> reg
  val vpsub_32u8 : reg -> reg -> reg
  val vpand_256 : reg -> reg -> reg
  val vpmaddubsw_256 : reg -> reg -> reg
  val vpmulh_16u16 : reg -> reg -> reg
  val vpmulhrs_16u16 : reg -> reg -> reg
  val vpsra_16u16 : reg -> int -> reg
  val vpsrl_16u16 : reg -> int -> reg
  val vpsrl_4u64 : reg -> int -> reg
  val vpsll_4u64 : reg -> int -> reg
  val vpackus_16u16 : reg -> reg -> reg
  val vpackss_16u16 : reg -> reg -> reg
  val vpshufb_256 : reg -> reg -> reg
  val vpcmpgt_16u16 : reg -> reg -> reg
  val vpmovmskb_u256u64 : reg -> reg
  val vpunpckl_32u8 : reg -> reg -> reg
  val vpextracti128 : reg -> int -> reg
  val vpinserti128 : reg -> reg -> int -> reg
  val vpblend_16u16 : reg -> reg -> int -> reg
  val vpslldq_256 : reg -> int -> reg
  val vpsrldq_256 : reg -> int -> reg
  val vpslldq_128 : reg -> int -> reg
  val vpsrldq_128 : reg -> int -> reg
end

(* ==================================================================== *)
module FromSpec () : S = struct
  (* ------------------------------------------------------------------ *)
  let specs =
    let specs = Filename.concat (List.hd Config.Sites.specs) "avx2.spec" in
    let specs = Circuit_spec.load_from_file ~filename:specs in
    let specs = BatMap.of_seq (List.to_seq specs) in
    specs

  let get_specification (name : symbol) : Ast.adef option =
    BatMap.find_opt name specs
 
  (* ------------------------------------------------------------------ *)
  let vpermd = Option.get (get_specification "VPERMD")

  let vpermd (r1 : reg) (r2 : reg) : reg =
    Circuit_spec.circuit_of_specification [r1; r2] vpermd

  (* ------------------------------------------------------------------ *)
  let vpermq = Option.get (get_specification "VPERMQ")

  let vpermq (r : reg) (i : int) : reg =
    Circuit_spec.circuit_of_specification [r; Circuit.w8 i] vpermq

  (* ------------------------------------------------------------------ *)
  let vpbroadcast_16u16 = Option.get (get_specification "VPBROADCAST_16u16")

  let vpbroadcast_16u16 (r : reg) : reg =
    Circuit_spec.circuit_of_specification [r] vpbroadcast_16u16

  (* ------------------------------------------------------------------ *)
  let vpadd_16u16 = Option.get (get_specification "VPADD_16u16")

  let vpadd_16u16 (r1 : reg) (r2 : reg) : reg =
    Circuit_spec.circuit_of_specification [r1; r2] vpadd_16u16

  (* ------------------------------------------------------------------ *)
  let vpadd_32u8 = Option.get (get_specification "VPADD_32u8")

  let vpadd_32u8 (r1 : reg) (r2 : reg) : reg =
    Circuit_spec.circuit_of_specification [r1; r2] vpadd_32u8

  (* ----------------------------------------------------------------- *)
  let vpsub_16u16 = Option.get (get_specification "VPSUB_16u16")

  let vpsub_16u16 (r1 : reg) (r2 : reg) : reg =
    Circuit_spec.circuit_of_specification [r1; r2] vpsub_16u16

  (* ------------------------------------------------------------------ *)
  let vpsub_32u8 = Option.get (get_specification "VPSUB_32u8")

  let vpsub_32u8 (r1 : reg) (r2 : reg) : reg =
    Circuit_spec.circuit_of_specification [r1; r2] vpsub_32u8

  (* ------------------------------------------------------------------ *)
  let vpand_256 = Option.get (get_specification "VPAND_256")

  let vpand_256 (r1 : reg) (r2 : reg) : reg =
    Circuit_spec.circuit_of_specification [r1; r2] vpand_256

  (* ------------------------------------------------------------------ *)
  let vpmaddubsw_256 = Option.get (get_specification "VPMADDUBSW_256")

  let vpmaddubsw_256 (r1 : reg) (r2 : reg) : reg =
    Circuit_spec.circuit_of_specification [r1; r2] vpmaddubsw_256

  (* ------------------------------------------------------------------ *)
  let vpmulh_16u16 = Option.get (get_specification "VPMULH_16u16")

  let vpmulh_16u16 (r1 : reg) (r2 : reg) : reg =
    Circuit_spec.circuit_of_specification [r1; r2] vpmulh_16u16

  (* ------------------------------------------------------------------ *)
  let vpmulhrs_16u16 = Option.get (get_specification "VPMULHRS_16u16")

  let vpmulhrs_16u16 (r1 : reg) (r2 : reg) : reg =
    Circuit_spec.circuit_of_specification [r1; r2] vpmulhrs_16u16

  (* ------------------------------------------------------------------ *)
  let vpsra_16u16 = Option.get (get_specification "VPSRA_16u16")

  let vpsra_16u16 (r : reg) (n : int) : reg =
    Circuit_spec.circuit_of_specification [r; Circuit.w8 n] vpsra_16u16

  (* ------------------------------------------------------------------ *)
  let vpsrl_16u16 = Option.get (get_specification "VPSRL_16u16")

  let vpsrl_16u16 (r : reg) (n : int) : reg =
    Circuit_spec.circuit_of_specification [r; Circuit.w8 n] vpsrl_16u16

  (* ------------------------------------------------------------------ *)
  let vpsrl_4u64 = Option.get (get_specification "VPSRL_4u64")

  let vpsrl_4u64 (r : reg) (n : int) : reg =
    Circuit_spec.circuit_of_specification [r; Circuit.w8 n] vpsrl_4u64

  (* ------------------------------------------------------------------ *)
  let vpsll_4u64 = Option.get (get_specification "VPSLL_4u64")

  let vpsll_4u64 (r : reg) (n : int) : reg =
    Circuit_spec.circuit_of_specification [r; Circuit.w8 n] vpsll_4u64

  (* ------------------------------------------------------------------ *)
  let vpslldq_256 = Option.get (get_specification "VPSLLDQ_256")

  let vpslldq_256 (r : reg) (n : int) : reg =
    Circuit_spec.circuit_of_specification [r; Circuit.w8 (8 * n)] vpslldq_256

  (* ------------------------------------------------------------------ *)
  let vpsrldq_256 = Option.get (get_specification "VPSRLDQ_256")

  let vpsrldq_256 (r : reg) (n : int) : reg =
    Circuit_spec.circuit_of_specification [r; Circuit.w8 (8 * n)] vpsrldq_256

  (* ------------------------------------------------------------------ *)
  let vpslldq_128 = Option.get (get_specification "VPSLLDQ_128")

  let vpslldq_128 (r : reg) (n : int) : reg =
    Circuit_spec.circuit_of_specification [r; Circuit.w8 (8 * n)] vpslldq_128

  (* ------------------------------------------------------------------ *)
  let vpsrldq_128 = Option.get (get_specification "VPSRLDQ_128")

  let vpsrldq_128 (r : reg) (n : int) : reg =
    Circuit_spec.circuit_of_specification [r; Circuit.w8 (8 * n)] vpsrldq_128

  (* ------------------------------------------------------------------ *)
  let vpackus_16u16 = Option.get (get_specification "VPACKUS_16u16")

  let vpackus_16u16 (r1 : reg) (r2 : reg) : reg =
    Circuit_spec.circuit_of_specification [r1; r2] vpackus_16u16  

  (* ------------------------------------------------------------------ *)
  let vpackss_16u16 = Option.get (get_specification "VPACKSS_16u16")

  let vpackss_16u16 (r1 : reg) (r2 : reg) : reg =
    Circuit_spec.circuit_of_specification [r1; r2] vpackss_16u16
    
  (* ------------------------------------------------------------------ *)
  let vpshufb_256 = Option.get (get_specification "VPSHUFB_256")

  let vpshufb_256 (r1 : reg) (r2 : reg) : reg =
    Circuit_spec.circuit_of_specification [r1; r2] vpshufb_256

  (* ------------------------------------------------------------------ *)
  let vpcmpgt_16u16 = Option.get (get_specification "VPCMPGT_16u16")

  let vpcmpgt_16u16 (r1 : reg) (r2 : reg) : reg =
    Circuit_spec.circuit_of_specification [r1; r2] vpcmpgt_16u16

  (* ------------------------------------------------------------------ *)
  let vpmovmskb_u256u64 = Option.get (get_specification "VPMOVMSKB_u256u64")

  let vpmovmskb_u256u64 (r : reg) : reg =
    Circuit_spec.circuit_of_specification [r] vpmovmskb_u256u64

  (* ------------------------------------------------------------------ *)
  let vpunpckl_32u8 = Option.get (get_specification "VPUNPCKL_32u8")

  let vpunpckl_32u8 (r1 : reg) (r2 : reg): reg =
    Circuit_spec.circuit_of_specification [r1; r2] vpunpckl_32u8

  (* ------------------------------------------------------------------ *)
  let vpextracti128 = Option.get (get_specification "VPEXTRACTI128")

  let vpextracti128 (r : reg) (i : int): reg =
    Circuit_spec.circuit_of_specification [r; Circuit.w8 i] vpextracti128

  (* ------------------------------------------------------------------ *)
  let vpinserti128 = Option.get (get_specification "VPINSERTI128")

  let vpinserti128 (r1 : reg) (r2 : reg) (i : int): reg =
    Circuit_spec.circuit_of_specification [r1; r2; Circuit.w8 i] vpinserti128

  (* ------------------------------------------------------------------ *)
  let vpblend_16u16 = Option.get (get_specification "VPBLEND_16u16")

  let vpblend_16u16 (r1 : reg) (r2 : reg) (i : int): reg =
    Circuit_spec.circuit_of_specification [r1; r2; Circuit.w8 i] vpblend_16u16
end
