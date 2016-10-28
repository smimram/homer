exception Timeout

let timeout sec f x =
  if Sys.os_type = "Win32" then
    (
      let rec alarm =
        let target = Unix.gettimeofday () +. sec in
        Gc.create_alarm (fun () -> if Unix.gettimeofday () >= target then raise Timeout)
      in
      try
        let ans = f x in
        Gc.delete_alarm alarm;
        ans
      with
      | e -> Gc.delete_alarm alarm; raise e
    )
  else
    (
      let set_timer sec =
        ignore
          (Unix.setitimer
             Unix.ITIMER_REAL
             { Unix.it_interval = 0.; Unix.it_value = sec })
      in
      let oldsig = Sys.signal Sys.sigalrm (Sys.Signal_handle (fun _ -> raise Timeout)) in
      set_timer sec;
      try
        let ans = f x in
        set_timer 0.;
        Sys.set_signal Sys.sigalrm oldsig;
        ans
      with
      | e ->
        set_timer 0.;
        Sys.set_signal Sys.sigalrm oldsig;
        raise e
    )
  (*
  let ans = ref None in
  let f x = ans := Some (f x) in
  let tf = Thread.create f x in
  let timer () = Thread.delay sec; Thread.kill tf in
  let _ = Thread.create timer () in
  Thread.join tf;
  match !ans with
  | Some ans -> ans
  | None -> raise Timeout
  *)

