type handle = {
  pre_uuid : int;
}

let capture session = { pre_uuid = Ec_llm_session.current_uuid session }

let rollback session h =
  Ec_llm_session.revert_to_uuid session ~target:h.pre_uuid

let commit h = h.pre_uuid
let captured_uuid h = h.pre_uuid
