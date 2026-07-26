(** Composition smoke driver. Wires up stub session backend + pool +
    publish point, then runs:
    1. The echo MCP_TOOL — verifies pool acquisition + publish emission.
    2. The admit-first OVERLAY_KIND — verifies the overlay contract
       shape and the forked-feed computation.

    Intended as a compile + behaviour gate for Phase 0b: if this binary
    builds and exits 0, the core contracts compose. *)

open Ecd_core
module Plug = Plugin.Make (Stub_session)

let assert_ok label = function
  | Ok x ->
      Printf.printf "ok: %s\n%!" label;
      x
  | Error e ->
      Printf.printf "FAIL: %s: %s\n%!" label (Error.to_string e);
      exit 1

let () =
  Eio_main.run @@ fun _env ->
  Eio.Switch.run @@ fun sw ->
  (* --- Pool --- *)
  let module P = Plug.Ctx.P in
  let pool =
    P.make ~sw
      {
        pool_size = 4;
        k_lsp = 1;
        k_mcp = 1;
        k_spec = 0;
      }
  in

  (* --- Publish point --- *)
  let (publish, publish_state) = Stub_publish.make () in

  (* --- Surface context --- *)
  let ctx : Plug.Ctx.t =
    {
      correlation = Correlation.of_client "smoke-1";
      switch = sw;
      deadline = None;
      pool;
      publish;
    }
  in

  (* --- Smoke 1: echo tool round-trip --- *)
  let result =
    assert_ok "echo tool invocation"
      (Echo_tool.T.invoke ctx (`Assoc [ ("msg", `String "hi") ]))
  in
  (match result with
   | `Assoc [ ("echoed", `String "hi") ] ->
       Printf.printf "ok: echo tool returned expected payload\n%!"
   | _ ->
       Printf.printf "FAIL: echo tool returned unexpected payload: %s\n%!"
         (Yojson.Safe.to_string result);
       exit 1);
  let events = Stub_publish.events_emitted publish_state in
  (match events with
   | [ Publish.State_changed _ ] ->
       Printf.printf "ok: publish point emitted 1 State_changed event\n%!"
   | _ ->
       Printf.printf "FAIL: expected 1 State_changed, got %d events\n%!"
         (List.length events);
       exit 1);

  (* --- Smoke 2: admit-first overlay --- *)
  let feed =
    Admit_first_overlay.O.apply ()
      [
        { Overlay.id = Sentence_id.stub_of_int 1; source = "rewrite /=." };
        { Overlay.id = Sentence_id.stub_of_int 2; source = "by algebra." };
      ]
  in
  (match feed with
   | [ "admit."; "by algebra." ] ->
       Printf.printf "ok: admit-first overlay produced expected feed\n%!"
   | _ ->
       Printf.printf "FAIL: admit-first overlay produced %s\n%!"
         (String.concat " | " feed);
       exit 1);

  P.close_all pool;
  Printf.printf "all smoke tests passed\n%!"
