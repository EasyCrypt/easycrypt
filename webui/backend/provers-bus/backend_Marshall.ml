(* $Id: helloworld.ml 1652 2011-08-03 21:50:30Z gerd $ *)

(* This example demonstrates some very basic features of Netplex:
    - Starting an "empty service", i.e. one that does not provide
      any network functionality. Nevertheless a service process is
      forked, and all the hook functions are executed.
    - Echo service: Opens a network port, and echos all lines
      sent to it
    - Simple RPC server: Implements the RPC "operation" from operation.x

    All three services are started from a single program.

    Note that there is a fundamental difference between "echo" and "operation":
    As echo is written in synchronous (blocking) style, and we have only
    one process, there can be at most one TCP connection to this service.
    In contrast to this, "operation" can serve many connections in parallel.
    This is a functionality of the RPC layer.

    Test helloworld:
      $ ./helloworld -fg -conf helloworld.cfg

    Then connect to "echo":
      $ netcat localhost 4343

    Connect to "operation":
      $ ./test_client -port 4444 foo

    Use netplex-admin for administration:

      $ ../../src/netplex/netplex-admin -list
      operation: Enabled 1 containers
	  rpc/operation @ inet:0.0.0.0:4444
      echo: Enabled 1 containers
	  echo_proto @ inet:0.0.0.0:4343
      empty: Enabled 1 containers
	  dummy @ -
      netplex.controller: Enabled 1 containers
	  admin @ local:/tmp/.netplex/netplex.controller/admin

      $ ../../src/netplex/netplex-admin -containers
      operation: Enabled 1 containers
	  rpc/operation @ inet:0.0.0.0:4444
	  Process 29390: selected
      echo: Enabled 1 containers
	  echo_proto @ inet:0.0.0.0:4343
	  Process 29389: selected
      empty: Enabled 1 containers
	  dummy @ -
	  Process 29388: selected
      netplex.controller: Enabled 1 containers
	  admin @ local:/tmp/.netplex/netplex.controller/admin
	  AttachedToCtrlProcess 29387: selected

      $ ../../src/netplex/netplex-admin -restart empty
      (and watch the log messages from "empty")

      $ ../../src/netplex/netplex-admin foo bar baz
      (and watch the log messages from all services)

      $ ../../src/netplex/netplex-admin -shutdown
      (and watch the log messages from all services)
 *)

open Printf

(**********************************************************************)

(* hello_hooks:

   Define the processor hooks so that a message is logged
   for each. Normally, one inherits from
   Netplex_kit.empty_processor_hooks and defines only the
   hooks that are needed.
 *)

class hello_hooks service_name : Netplex_types.processor_hooks =
object(self)
  inherit Netplex_kit.empty_processor_hooks()

  method post_add_hook _ _ =
    Netlog.logf `Info "%s: post_add_hook" service_name

  method post_rm_hook _ _ =
    Netlog.logf `Info "%s: post_rm_hook" service_name

  method pre_start_hook _ _ _ =
    Netlog.logf `Info "%s: pre_start_hook" service_name

  method post_start_hook _ =
    Netlog.logf `Info "%s: post_start_hook" service_name

  method pre_finish_hook _ =
    Netlog.logf `Info "%s: pre_finish_hook" service_name

  method post_finish_hook _ _ _ =
    Netlog.logf `Info "%s: post_finish_hook" service_name

  method receive_message _ msg args =
    Netlog.logf `Info "%s: receive_message(\"%s\", [%s])"
      service_name
      (String.escaped msg)
      (String.concat ","
	 (List.map
	    (fun arg -> "\"" ^ String.escaped arg ^ "\"")
	    (Array.to_list args)))

  method receive_admin_message _ msg args =
    Netlog.logf `Info "%s: receive_admin_message(\"%s\", [%s])"
      service_name
      (String.escaped msg)
      (String.concat ","
	 (List.map
	    (fun arg -> "\"" ^ String.escaped arg ^ "\"")
	    (Array.to_list args)))

  method system_shutdown () =
    Netlog.logf `Info "%s: system_shutdown" service_name

  method shutdown() =
    Netlog.logf `Info "%s: shutdown" service_name

  method global_exception_handler e =
    Netlog.logf `Info "%s: global_exception_handler(%s)"
      service_name
      (Netexn.to_string e);
    true
end

(**********************************************************************)
(* Backend service                                                       *)
(**********************************************************************)

let backend_service_factory() : Netplex_types.processor_factory =
  ( object
      method name = "backend_service"

      method create_processor ctrl_cfg cf addr =
	( object (self)
	    inherit hello_hooks "backend_service"

	    method supported_ptypes = [ `Multi_processing; `Multi_threading ]

	    method process ~when_done cont fd proto =
	      Netlog.logf `Info "backend_service: process(%s)" proto;
	      (* fd is non-blocking, but we want it again blocking: *)
	      Unix.clear_nonblock fd;
	      (* We have to call when_done under all circumstances, so
                 catch exceptions here
	       *)
	      try
		(* We cannot use here in_channel/out_channel as we have
                   a bidirectional connection. Netchannels has something
                   for us:
		 *)
		let rch = new Netchannels.socket_descr fd in
		(* On top of this, create buffered channels *)
		let ich =
		  Netchannels.lift_in
		    (`Raw (rch :> Netchannels.raw_in_channel)) in
		let och =
		  Netchannels.lift_out
		    (`Raw (rch :> Netchannels.raw_out_channel)) in
		( try
		    while true do
		      (* Read a line from ich, echo to och: *)
		      let line = ich # input_line() in
                      let lineM = Marshal.to_string line [] in
		      och # output_string lineM;
		      och # flush();
		    done;
		    assert false  (* don't reach this point *)
		  with
		    | End_of_file ->
			(* We finally get End_of_file from input_line *)
			ich # close_in();
			och # close_out()
		    | error ->
			ich # close_in();
			och # close_out();
			raise error
		);
		(* Done with it: *)
		when_done()
	      with
		| error ->
		    (* We have to ensure that when_done is always called,
                       even on error.
		     *)
		    Netlog.logf `Err
		      "Exception while echoing: %s" (Netexn.to_string error);
		    when_done();
		    (* We could raise the exception here again... *)
	  end
	)
    end
  )


(**********************************************************************)
(* Main                                                               *)
(**********************************************************************)

let main() =
  let (opt_list, cmdline_cfg) = Netplex_main.args() in

  let use_mt = ref false in

  let opt_list' =
    [ "-mt", Arg.Set use_mt,
      "  Use multi-threading instead of multi-processing";

      "-debug", Arg.String (fun s -> Netlog.Debug.enable_module s),
      "<module>  Enable debug messages for <module>";

      "-debug-all", Arg.Unit (fun () -> Netlog.Debug.enable_all()),
      "  Enable all debug messages";

      "-debug-list", Arg.Unit (fun () ->
                                 List.iter print_endline (Netlog.Debug.names());
                                 exit 0),
      "  Show possible modules for -debug, then exit";
   ] @ opt_list in

  Arg.parse
    opt_list'
    (fun s -> raise (Arg.Bad ("Don't know what to do with: " ^ s)))
    (sprintf "usage: %s [options]" (Filename.basename Sys.argv.(0)));

  let parallelizer =
    if !use_mt then
      Netplex_mt.mt()     (* multi-threading *)
    else
      Netplex_mp.mp() in  (* multi-processing *)

  Netplex_main.startup
    parallelizer
    Netplex_log.logger_factories   (* allow all built-in logging styles *)
    Netplex_workload.workload_manager_factories (* ... all ways of workload management *)
    [  backend_service_factory() ]
    cmdline_cfg


let () =
  Netsys_signal.init();
  main()
