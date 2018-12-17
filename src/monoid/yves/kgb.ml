(** KGB completion procedure **)

open Standard
open FreeMonoid

(* Replacing a generator, eg if a rule x -> y exists with x & y generators. *)
let gen_remove i gens =
  let n = Array.length gens in
  if i = 0
  then Array.sub gens 1 (n-1)
  else 
    if i = n
    then Array.sub gens 0 (n-1)
    else 
      let gens1 = Array.sub gens 0 i in
      let gens2 = Array.sub gens (i+1) (n-i-1) in 
      Array.append gens1 gens2

let gen_replace i j k = 
  if i = j
  then k
  else
    if k = i 
    then 
      if j < i
      then j
      else j-1
    else
      if k > i
      then k-1
      else k

let word_replace i j u =
  Array.map (gen_replace i j) u

let rule_replace i j (u, v) =
  (word_replace i j u, word_replace i j v)

let rules_replace i j rules = 
  IMap.map (rule_replace i j) rules  
  
let replace x y rs =
  if x = y 
  then rs
  else
    let i = Array.index rs.generators x in
    let j = Array.index rs.generators y in
    {
      rs with 
	generators = gen_remove i rs.generators;
	rules = rules_replace i j rs.rules;
    }
  
(* Splits a word u as xv, with x a generator. Fails if u is empty. *)
let head_split u = 
  let n = Array.length u in 
  assert (n > 0);
  let x = u.(0) in
  let v = Array.sub u 1 (n - 1) in
  x, v

(* Splits a length-two word as a pair (x, y) of generators *)
let split u =
  assert (Array.length u = 2);
  (u.(0), u.(1))

(* Returns the list of length-two factorisations yz of a generator x, ie the yz such that yz -> x exists in rs *)
let factorisations rs x =
  let rules = IMap.to_list (rs.rules) in 
  let fact_rules = 
    List.filter 
      (fun (u, v) -> (Array.length u = 2) && (v = [|x|]))
      rules
  in 
  List.map (fun (u, v) -> split u) fact_rules

(* Right-divisors *)
let immediate_right_divisors rs x =
  let facts = factorisations rs x in
  List.map (fun (y, z) -> z) facts

let rec right_divisors rs x = 
  let ird = immediate_right_divisors rs x in
  List.append ird (List.concat (List.map (right_divisors rs) ird))

let is_right_divisor rs x y =
  let rdivs = right_divisors rs y in
  List.exists (fun z -> z = x) rdivs

(* Exception raised by Garside order when words are not comparable *)
exception Not_comparable

(* Garside partial order on words of length 2 : xx' < yy' if x' right-divides y' *)
let garleq rs u v = 
  assert (Array.length u = 2);
  assert (Array.length v = 2);
  if u = v 
  then 0
  else
    let (x, x') = split u in
    let (y, y') = split v in
    if is_right_divisor rs x' y' 
    then -1
    else 
      if is_right_divisor rs y' x'
      then 1
      else raise Not_comparable

let is_garside_compatible rs (u, v) = 
  let m = Array.length u in
  let n = Array.length v in
  match m, n with
    | 2, 1 -> true
    | 2, 2 -> (
      try 
	match garleq rs u v with
	  | 1 -> true
	  | _ -> false
      with
	| Not_comparable -> false
    )
    | _, _ -> false

let garside_filter rs i (u, v) = is_garside_compatible rs (u, v)
	
(* Add generator w and rule word w -> gen w if w is not already present *)
let add_gen rs w = 
  if FreeMonoid.has_generator rs w
  then rs
  else (
    Printf.printf "Generator %s added.\n" w;
    LangMonoid.rgen rs w
  )

(* Quadratification of a word u : if u=xv with |v|>1, then adds generator v to rs and rule word v -> gen v *)
let rec word_quadratification ?(bound=0) rs u = 
  if (Array.length u <= 2)
  then rs 
  else
    let wu = Word.to_string_no_par rs u in
    if (String.length wu > bound) && (bound > 0) 
    then rs 
    else
      let (x, v) = head_split u in
      let w = Word.to_string_no_par rs v in
      let rs = add_gen rs w in
      word_quadratification rs v

(* Quadratification of a rewriting system *)
let quadratification ?(bound=0) rs = 
  let rules = IMap.to_list (rs.rules) in
  let rec words_in_rules = function
    | [] -> []
    | (u, v) :: rules -> u :: v :: (words_in_rules rules)
  in 
  let words = words_in_rules rules in
  let rec quad_aux rs = function
    | [] -> rs
    | u :: words -> quad_aux (word_quadratification ~bound rs u) words
  in 
  quad_aux rs words

(* Cleanup rules *)
let is_unary i (u, v) = Word.length u = 1 && Word.length v = 1

let unary_rules rs = IMap.filter is_unary rs.rules

let remove_unary_rules rs =
  let rec aux rs = function
    | [] -> rs
    | (x, y) :: rules -> 
      let wx = Word.to_string rs x in
      let wy = Word.to_string rs y in
      let i = Array.index rs.generators wx in
      let j = Array.index rs.generators wy in
      let rs = replace wx wy rs in
      let rules = List.map (rule_replace i j) rules in
      aux rs rules
  in aux rs (IMap.to_list (unary_rules rs))

let cleanup_rule rs r =
  let (u, v) = IMap.find r rs.rules in
  if u = v
  then rm_rule rs r
  else 
    if Word.length u = 1 && Word.length v = 1 
    then 
      let wu = Word.to_string_no_par rs u in
      let wv = Word.to_string_no_par rs v in
      let wu', wv' = if String.compare wu wv < 0 then wv, wu else wu, wv in
      replace wu' wv' (rm_rule rs r)
    else rs

let cleanup rs = 
  let rules = List.map (fun (x,y) -> x) (IMap.bindings rs.rules) in
  let rec aux rs = function
    | [] -> rs
    | r :: rules -> 
      aux (cleanup_rule rs r) rules
  in aux rs rules

(* Canonisation using only Garside-compatible rules *)

(** À Faire : remanier les canonise génériques pour ne pas dupliquer le code **)

let garside_canonize_right rs =
  let f rs = 
    let rules = IMap.filter (garside_filter rs) rs.rules in
    let rs = ref rs in
    try 
      IMap.iter
	(fun r (r1,r2) ->
	  let r2' = normalize ~rules !rs r2 in
	  if r2' <> r2 then
            (
	      rs := rm_rule !rs r;
              rs := add_rule !rs (r1, r2');
	      raise Exit;
            )
	) !rs.rules;
      !rs
    with 
      | Exit -> !rs
  in fixpoint f rs

let garside_canonize_dup rs =
  let rs = ref rs in
  IMap.iter_pairs ~reflexive:false
    (fun r (r1,r2) s (s1,s2) ->
      if r1 = s1 && r2 = s2 
      then rs := rm_rule !rs s
    ) 
    !rs.rules;
  !rs
    
let garside_canonize_left ~lt rs =
  let f rs =
    let rules = IMap.filter (garside_filter rs) rs.rules in
    let rs = ref rs in
    try
      IMap.iter
	(fun r (r1,r2) ->
	  IMap.iter 
	    (fun s (s1,s2) ->
	      if (r,r1,r2) <> (s,s1,s2) 
	      then 
		for o = 0 to Array.length r1 - Array.length s1 do
		  if Array.included o s1 r1 
		  then
		    let u = Array.sub r1 0 o in
                    let v = Array.sub_right r1 0 (Array.length r1 - Array.length s1 - o) in
		    let r1' = normalize ~rules !rs (W.concat [u;s2;v]) in
		    rs := rm_rule !rs r;
		    if r1' <> r2 then (
		      let u,v = if lt !rs r1' r2 then r2,r1' else r1',r2 in
		      rs := add_rule ~dup:false !rs (u,v);
		    );
		    raise Exit (* Restart from the begining as soon as we changed something. *)
		done
	    ) 
	    rules
	)
	!rs.rules;
      !rs
    with 
      | Exit -> !rs
  in
  fixpoint f rs

let garside_canonisation ~lt rs = 
  let rs = garside_canonize_right rs in
  let rs = garside_canonize_dup rs in
  let rs = garside_canonize_left ~lt rs in
  rs 

(* Garsidification *)
let garsidification_rule ?(bound=0) rs r =
  let (u, v) = IMap.find r rs.rules in
  if (Array.length u = 2) && (Array.length v = 2)
  then 
    let wu = Word.to_string_no_par rs u in
    let wv = Word.to_string_no_par rs v in
    if (String.length wu > bound || String.length wv > bound) && (bound > 0)
    then rs
    else 
      let comp = 
	try garleq rs u v
	with Not_comparable -> 0
      in 
      match comp with 
      | 1 -> rs
      | -1 -> add_rule (rm_rule rs r) (v, u)
      | 0 -> 
	let w = if String.compare wu wv < 0 then wu else wv in
	let rs = add_gen rs w in
	let rs = rm_rule rs r in
	let iw = Array.index rs.generators w in
	let rs = add_rule rs (u, [|iw|]) in
	let rs = add_rule rs (v, [|iw|]) in
	rs
      | _ -> failwith "not possible"
  else rs

let garsidification ?(bound=0) rs =
  let rules = List.map (fun (x,y) -> x) (IMap.bindings rs.rules) in
  let rec aux rs = function
    | [] -> rs
    | r :: rules -> 
      aux (garsidification_rule ~bound rs r) rules
  in aux rs rules

(* Ordre à voir *)
let lt =
  let label_lt s t = 
    let ls = String.length s in
    let lt = String.length t in
    if ls < lt then true
    else if lt < ls then false
    else s < t
  in 
  FreeMonoid.weightlex ~rev:true label_lt

(* KGB *)
let garside_cleanup ~lt rs = 
  let aux rs = fixpoint cleanup (garside_canonisation ~lt rs) in
  fixpoint aux rs

let garside_completion_step ~lt rs = 
  let rules = IMap.filter (garside_filter rs) rs.rules in 
  completion_step ~rules ~lt rs
    
let rec gar_aux n ~lt rs =
  Printf.printf "\n=== GAR %i ===\n" n;
  let rs' = garside_cleanup ~lt (garsidification ~bound:n rs) in
  if rs' = rs 
  then quad_aux n ~lt rs
  else rs'

and quad_aux n ~lt rs =
  Printf.printf "\n=== QUAD %i ===\n" n;
  let rs' = garside_cleanup ~lt (quadratification ~bound:n rs) in
  if rs' = rs 
  then gar_aux (n+1) ~lt rs
  else rs'

(** Voir comment passer à l'ordre "revweightlex" automatiquement au début de KGB **)

let rec kgb ~lt rs = 
  Printf.printf "\n=== KGBS ===\n";
  let rs = fixpoint (fun rs -> garside_cleanup ~lt (garside_completion_step ~lt rs)) rs in
  if IMap.for_all (garside_filter rs) rs.rules
  then rs
  else kgb ~lt (gar_aux 2 ~lt rs)

(* Interactive functions *)
let () = 

  LangMonoid.register "replace" "Replacement of a generator by another one" 2
    (fun rs a -> replace a.(0) a.(1) rs);

  LangMonoid.register "remunary" "Removal of unary rules" 0
    (fun rs a -> remove_unary_rules rs);

  LangMonoid.register "clean" "Cleanup." 0
    (fun rs a -> cleanup rs);

  LangMonoid.register "gcan" "Gaside canonisation." 0
    (fun rs a -> garside_cleanup ~lt rs);
      
  LangMonoid.register "quad" "Quadratification." 1 
    (fun rs a -> 
      let bound = int_of_string a.(0) in
      let rs = quadratification ~bound rs in
      let rs = garside_cleanup ~lt rs in
      rs
    );

  LangMonoid.register "gar" "Garsidification." 1
    (fun rs a -> 
      let bound = int_of_string a.(0) in
      let rs = garsidification ~bound rs in
      let rs = garside_cleanup ~lt rs in
      rs
    );

  LangMonoid.register "kgbs" "One-step KGB completion." 0
    (fun rs a -> 
      let rs = garside_completion_step ~lt rs in
      let rs = garside_cleanup ~lt rs in
      rs
    );

  LangMonoid.register "kgb" "KGB completion." 0
    (fun rs a -> 
      LangMonoid.order := "revweightlex";
      kgb ~lt rs
    );
