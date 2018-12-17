(** Part of the language which is specific to monoids. *)

open Standard

module M = FreeMonoid

let rs = ref (M.create ())

(** Human-readable word printing. *)
let w s =
  let s = if s = "\"\"" || s = "1" || s = "ε" then "" else s in
  M.Word.of_string !rs s
let sw w = M.Word.to_string !rs w
let sr = M.CRules.to_string
let printf = Lang.printf

let print_rs () = 
  if !Lang.verbose then
    (
      printf "%s\n%!" (M.to_string !rs);
      let n = M.nb_rules !rs in
      if n > 5 then 
	printf "We have %d generators and %d rules.\n%!" (M.nb_generators !rs) n
    )
  else ()

let handlers = ref ([] : (string * (string * int * (M.rs -> string array -> M.rs))) list)

(** Register a new command *)
let register ?(undo=true) name doc args f =
  let mode = "monoid" in
  let f a =
    let rsold = !rs in
    rs := f !rs a;
    if !rs <> rsold then print_rs ();
    fun () -> rs := rsold
  in
  if undo then
    Lang.register_with_undo ~mode name doc args f
  else
    let f a = let _ = f a in () in
    Lang.register ~mode name doc args f

let () =
  register ~undo:false "rs" "Display current rewriting system." 0 (fun rs a -> print_rs (); rs);
  register "new" "Create an empty rewriting system." 1 (fun rs a -> M.add_generators (M.create ()) (int_of_string a.(0)));
  register "gen" "Add a generator." (-1) (fun rs a -> Array.fold_left (fun rs name -> M.add_generator rs ~name) rs a);
  register "gens" "Add a specified number of generators." 1 (fun rs a -> M.add_generators rs (int_of_string a.(0)))

(** {2 Operations on orders} *)

let order = ref "deglex"
    
let orders =
  let label_lt s t =
    let ls = String.length s in
    let lt = String.length t in
    if ls < lt then true
    else if lt < ls then false
    else s < t
  in
  let revlabel_lt s t =
    let ls = String.length s in
    let lt = String.length t in
    if ls < lt then true
    else if lt < ls then false
    else s > t
  in
  let revlenlabel_lt s t =
    let ls = String.length s in
    let lt = String.length t in
    if ls > lt then true
    else if lt > ls then false
    else s < t
  in
  let genorder_lt s t =
    let i = Array.index (!rs).M.generators s in
    let j = Array.index (!rs).M.generators t in
    if i < j then true 
    else false
  in
  let revgenorder_lt s t =
    let i = Array.index (!rs).M.generators s in
    let j = Array.index (!rs).M.generators t in
    if i > j then true 
    else false
  in
  [
   "lex", M.lexico label_lt;
   "revlex", M.lexico revlabel_lt;
   "deglex", M.deglex label_lt;
   "deglex2", M.deglex genorder_lt;
   "revdeglex", M.deglex revlabel_lt;
   "revdeglex2", M.deglex revgenorder_lt;
   "codeglex", M.deglex ~co:true label_lt;
   "revlendeglex", M.deglex revlenlabel_lt;
   "lablex", M.lablex ~rev:false;
   "revlablex", M.lablex ~rev:true;
   "weightlex", M.weightlex ~rev:false label_lt;
   "revweightlex", M.weightlex ~rev:true label_lt;
 ]

let lt rs u v = (List.assoc !order orders) rs u v

let compare rs u v =
  if u = v then 0
  else if lt rs u v then -1
  else 1

let () =
  let doc = "Set completion order ("^String.concat ", " (List.map fst orders)^")." in
  register "order" doc (-1)
    (fun rs a ->
      if Array.length a <> 1 then
        printf "Current order: %s.\n%!" !order
      else if not (List.mem a.(0) (List.map fst orders)) then
        printf "Unknown order: %s.\n%!" a.(0)
      else
        (
	  order := a.(0);
	  M.IMap.iter (fun _ (r1,r2) -> if not (lt rs r2 r1) then printf "Warning: rule %s -> %s does not respect order.\n%!" (sw r1) (sw r2)) rs.M.rules
        );
      rs
    )

(** {2 Rules and definable generators} *)

let add_rule rs (s,t) =
  if not (lt rs t s) then printf "Warning: rule not compatible with order.\n%!";
  M.add_rule rs (s,t)

let () =
  register "rule" "Add a rule." 2
    (fun rs a ->
      try
	let w0 = w a.(0) in
	let w1 = w a.(1) in
	add_rule rs (w0, w1)
      with Assert_failure _ -> failwith "Undefined generator(s)."
    );
  register "unrule" "Remove a rule." 1 (fun rs a -> M.rm_rule rs (M.rule_of_string a.(0)))

let rgen rs g =
  let rs = M.add_generator rs ~name:g in
  let l = w g in
  let r = M.Word.of_generator ((M.nb_generators rs) - 1) in
  let rs = add_rule rs (l, r) in
  rs

let () =
  register "rgen" "Add a definable generator." (-1) (fun rs a -> Array.fold_left rgen rs a);
  register "rgensw" "Add subwords of a word as definable generators." 1
    (fun rs a ->
      let w = a.(0) in
      let n = String.length w in
      let rs = ref rs in
      for x = 0 to 1 lsl n - 1 do
        let sw = ref "" in
        for i = 0 to n - 1 do
          if x land (1 lsl i) <> 0 then sw := !sw ^ String.of_char w.[i]
        done;
        let sw = !sw in
        if String.length sw > 1 then rs := rgen !rs sw
      done;
      !rs
    );
  register "rsw" "Add subwords of left members of rules as definable generators." 0
    (fun rs a -> List.fold_left rgen rs (M.rules_sw rs));
