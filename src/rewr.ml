(** Main. *)

open Stdlib
open Timeout

let interactive = ref true

let () = Printexc.record_backtrace true
    
let () =
  let fname = ref None in
  Arg.parse
    [
      "-b", Arg.Clear interactive, " Batch mode.";
      "--batch", Arg.Clear interactive, " Batch mode.";
      "-q", Arg.Clear Lang.verbose, " Quiet mode.";
      "--quiet", Arg.Clear Lang.verbose, " Quiet mode.";
    ]
    (fun f -> fname := Some f)
    "rewr [options] [file]";
  let ic =
    match !fname with
    | Some f -> (* Lang.verbose := false; *) open_in f
    | None -> stdin
  in
  let ic = ref ic in
  try
    while true do
      try
        if !fname = None then Printf.printf "# %!";
        let l = input_line !ic in
	let l = 
	  if l <> "" && l.[String.length l - 1] = '\r' 
	  then String.sub l 0 (String.length l - 1) 
	  else l
	in
        if !fname <> None && !Lang.verbose then Printf.printf "# %s\n%!" l;
        (
          try
            (* if Sys.os_type = "Win32" then Lang.cmd l else *)
            timeout !Lang.timeout Lang.cmd l
          with
          | Timeout -> Printf.printf "\nTimeout!\n%!"
          | Failure s -> Printf.printf "Error: %s\n%!" s
          | e -> Printf.printf "%s\n%s\n%!" (Printexc.to_string e) (Printexc.get_backtrace ())
        )
      with
      | End_of_file ->
         close_in !ic;
        if !interactive then
          (
            fname := None;
	    Lang.verbose := true;
	    (* Lang.cmd "rs"; *)
	    (* Lang.cmd "order"; *)
            ic := stdin;
          )
        else raise Exit
    done
  with
  | Exit -> ()
