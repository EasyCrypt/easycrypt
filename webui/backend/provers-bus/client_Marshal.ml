open Printf

let open_connection sockaddr =
   let domain = Unix.PF_INET in
   let sock = Unix.socket domain Unix.SOCK_STREAM 0
   in try Unix.connect sock sockaddr ;
          (Unix.in_channel_of_descr sock , Unix.out_channel_of_descr sock)
     with exn -> Unix.close sock ; raise exn

let shutdown_connection inchan =
   Unix.shutdown (Unix.descr_of_in_channel inchan) Unix.SHUTDOWN_SEND

let main_client client_fun  =

  let server = "localhost" in
        let server_addr =
          try  Unix.inet_addr_of_string server
          with Failure("inet_addr_of_string") ->
                 try  (Unix.gethostbyname server).Unix.h_addr_list.(0)
                 with Not_found ->
                        Printf.eprintf "%s : Unknown server\n" server ;
                        exit 2
        in try
             let port = 4343 in
             let sockaddr = Unix.ADDR_INET(server_addr,port) in
             let ic,oc = open_connection sockaddr
             in client_fun ic oc ;
                shutdown_connection ic
           with Failure("int_of_string") -> Printf.eprintf "bad port number";
                                            exit 2

let client_fun ic oc =

   try
     while true do
       print_string  "Request : " ;
       flush stdout ;
       (* Send *)
       let line = input_line stdin in
       let lineM = Marshal.to_string line [] in
       output_string oc lineM ;
       flush oc ;
       (* Receive*)
       let r = (Marshal.from_channel ic : string)
       in Printf.printf "Response : %s\n\n" r;
          if r = "END" then ( shutdown_connection ic ; raise Exit) ;
     done
   with
       Exit -> exit 0
     | exn -> shutdown_connection ic ; raise exn

let go_client () = main_client client_fun

let _ = go_client ()
