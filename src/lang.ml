(** General implementation of the language. *)

open Standard

let print_string = ref print_string
let print s = !print_string s
let printf fmt = Printf.ksprintf print fmt

let verbose = ref true

(** Stack of functions to undo last actions. *)
let undo = ref []
(** Timeout for commands. *)
let timeout = ref 5.
(** Registered commands. *)
let handlers = ref []
(** Current mode: only commands with this mode or global ones are available. *)
let mode = ref "monoid"

(** Register a new command. If the number of arguments is negative then it is
    considered as variable. *)
let register ?mode name doc args (f : string array -> unit) =
  let f a = f a; None in
  handlers := ((mode, name), (doc, args, f)) :: !handlers

(** Register a new command which can undo its effect. The function should return
    a function to undo its effect. *)
let register_with_undo ?mode name doc args (f : string array -> unit -> unit) =
  let f a = Some (f a) in
  handlers := ((mode, name), (doc, args, f)) :: !handlers

let cmd cmd =
  let cmd = String.split_char cmd ' ' in
  let cmd = List.filter (fun s -> s <> "") cmd in
  match cmd with
  | cmd::_ when cmd.[0] = '#' -> ()
  | cmd::args ->
     let _, a, f =
       try
         let rec aux = function
           | ((md,name), c)::_ when (md = None || md = Some !mode) && name = cmd -> c
           | _::l -> aux l
           | [] -> raise Not_found
         in
       (* List.assoc cmd !handlers *)
         aux !handlers
       with
       | Not_found -> failwith (Printf.sprintf "Unknown command %s." cmd)
     in
     let args = Array.of_list args in
     if Array.length args <> a && a >= 0 then failwith (Printf.sprintf "Command %s requires %d arguments." cmd a);
     (
       match f args with
       | Some u -> undo := u :: !undo
       | None -> ()
     )
  | [] -> ()

let () =
  register "quit" "Quit the program." 0 (fun _ -> exit 0);
  register "exit" "Quit the program." 0 (fun _ -> exit 0);
  register "timeout" "Set timeout duration (in seconds)." (-1) (fun a ->
    if Array.length a = 0 then
      printf "Timeout: %f\n" !timeout
    else
      let t = float_of_string a.(0) in
      if t <= 0. then failwith "Timeout must be positive.";
      timeout := t
  );
  register "undo" "Undo last operation." 0
    (fun _ ->
      match !undo with
      | f::u ->
         f ();
        undo := u
      | [] -> ()
    );
  register "help" "Display this help." 0 (fun a ->
    let handlers = List.sort (fun ((_,n1),_) ((_,n2),_) -> compare n1 n2) !handlers in
    let cmd =
      List.map (fun ((md,name),(help,_,_)) ->
        if md = None || md = Some !mode then
          Printf.sprintf "- %s: %s\n" name help
        else
          ""
      ) handlers
    in
    let cmd = String.concat "" cmd in
    printf "Available commands:\n%s%!" cmd
  );
  register "mode" "Change mode." (-1) (fun a ->
    if Array.length a = 0 then
      printf "%s\n%!" !mode
    else
      let md = a.(0) in
      if List.for_all (fun ((m,_),_) -> m <> Some md) !handlers then
        failwith "Unknown mode."
      else
        (
          if !verbose then printf "Mode %s activated!\n" md;
          mode := md
        )
  );
  register "quiet" "Print as little messages as possible." 0 (fun a -> verbose := false)

