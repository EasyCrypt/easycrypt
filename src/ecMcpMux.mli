(* -------------------------------------------------------------------- *)
(* The session multiplexer behind [easycrypt mcp -sessions]: an MCP
   server on stdio that runs one child [easycrypt mcp] engine per
   session name and forwards each tool call to the session it names.
   Sessions are independent engines, so several agents can drive one
   server without sharing a proof state. *)

(* Serve until end of input, then kill every child and exit. Never
   returns. *)
val run : EcOptions.mcp_option -> 'a
