(** Trivial [MCP_TOOL] smoke test. Exercises, via the composition seam:
    - scratch-pool acquisition through [Surface_ctx];
    - cancellation token availability;
    - publish-point emission of a [State_changed] event. *)

open Ecd_core

module Plug = Plugin.Make (Stub_session)

let fresh_seq =
  let r = ref 0 in
  fun () -> incr r; !r

module T : Plug.MCP_TOOL = struct
  let name = "echo"

  let schema : Yojson.Safe.t =
    `Assoc
      [ ("type", `String "object");
        ("properties",
          `Assoc [ ("msg", `Assoc [ ("type", `String "string") ]) ]);
        ("required", `List [ `String "msg" ]) ]

  let invoke (ctx : Plug.Ctx.t) (params : Yojson.Safe.t) =
    let msg =
      match params with
      | `Assoc fields -> (
          match List.assoc_opt "msg" fields with
          | Some (`String m) -> Ok m
          | _ -> Error (Error.Parse_error { detail = "missing string 'msg'" }))
      | _ -> Error (Error.Parse_error { detail = "expected object params" })
    in
    match msg with
    | Error e -> Error e
    | Ok msg -> (
        match
          Plug.Ctx.P.acquire_scratch ctx.pool ~kind:`Mcp
            ~corr:ctx.correlation
        with
        | Error e -> Error e
        | Ok session ->
            let exec_res =
              Stub_session.exec session ~corr:ctx.correlation
                ~sentence_class:`Executable
                ~source:(Printf.sprintf "(* echo: %s *)" msg)
            in
            Plug.Ctx.P.release ctx.pool session;
            (match exec_res with
             | Error e -> Error e
             | Ok ok ->
                 ctx.publish.publish
                   (Publish.State_changed
                      {
                        document_uri = "stub://smoke";
                        cas = "cas-stub";
                        current_sentence = ok.sentence_id;
                        seq = fresh_seq ();
                        origin_correlation = Some ctx.correlation;
                      });
                 Ok (`Assoc [ ("echoed", `String msg) ])))
end
