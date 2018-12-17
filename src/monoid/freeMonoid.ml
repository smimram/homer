(** Free monoids. *)

open Standard

(** A letter in a signature. *)
type letter = int

(** A word. *)
type word = letter array

(** A rule in a signature. *)
type rule = int

let string_of_rule (r : rule) =
  let n = r / 26 in
  let r = r mod 26 in
  let c = char_of_int (r + int_of_char 'A') in
  if n = 0 then String.of_char c
  else String.make 1 c ^ string_of_int n

let rule_of_string s : rule =
  let c = int_of_char s.[0] in
  assert (int_of_char 'A' <= c && c <= int_of_char 'Z');
  let c = c - int_of_char 'A' in
  if String.length s = 1 then
    c
  else
    let n = String.sub s 1 (String.length s - 1) in
    let n = int_of_string n in
    c + n * 26

(** Things indexed by integers (used for rules). *)
module IMap = struct
  include Map.Make (struct type t = int let compare (x:int) (y:int) = compare x y end)

  let rec exists p m =
    fold (fun v d x -> p v d || x) m false

  let for_all p m = not (exists (fun v d -> not (p v d)) m)

  let to_list m = fold (fun n r l -> r::l) m []

  let find_map f m =
    let ans = ref None in
    try
      iter
        (fun i x ->
          let y = f i x in
          if y <> None then (ans := y; raise Exit))
        m;
      raise Exit
    with
    | Exit -> get_some !ans

  (** Iterate over pairs of keys. *)
  let iter_pairs ?(symmetric=false) ?(reflexive=true) f m =
    iter
      (fun i1 x1 ->
        iter
          (fun i2 x2 ->
            if (symmetric && i1 <> i2) || i1 < i2 || (reflexive && i1 = i2) then f i1 x1 i2 x2
          ) m
      ) m

  let find r m =
    try
      find r m
    with
      | Not_found -> failwith (Printf.sprintf "Cannot find rule %s." (string_of_rule r))

  let cardinal m = List.length (to_list m)
end

(** A contextualized word. *)
type cword = word * word * word

(** A contextualized rule. *)
type crule = word * rule * word

(** A rewriting path. *)
type crules = crule list

(** A thing which might be inverted. *)
type 'a inv = Inj of 'a | Inv of 'a

(** A rewriting system. *)
type rs =
  {
    (** Generators together with their name. *)
    generators : string array;
    (** Number of rules (dead or alive). *)
    nrules : int;
    (** Rules. *)
    rules : (word * word) IMap.t;
    (** Equations. *)
    (*equations : (word * word) List ;*)
  }

module Word = struct
  include Array

  type t = word

  let empty : t = [||]

  let is_empty w =
    length w = 0

  let singleton x : t = [|x|]

  let append : t -> t -> t = append

  let to_string rs w =
    match w with
    | [||] -> "\"\""
    | _ ->
       let ans = ref "" in
       for i = 0 to length w - 1 do
         let a = rs.generators.(w.(i)) in
         let a = if String.length a = 1 then a else "("^a^")" in
         ans := !ans ^ a
       done;
       !ans

  let stripchars s cs =
  let cs = Bytes.of_string cs in
  let len = String.length s in
  let res = Bytes.create len in
  let rec aux i j =
    if i >= len then Bytes.sub res 0 j
    else if Bytes.contains cs s.[i] then
      aux (succ i) (j)
    else begin
      Bytes.set res j s.[i];
      aux (succ i) (succ j)
    end
  in
  Bytes.to_string (aux 0 0)

  let to_string_no_par rs w = 
    stripchars (to_string rs w) "()"

  let eq : t -> t -> bool = (=)

  (** Degree of a word (the degree of a letter is the number of letters in its
      actual writing). *)
  let degree rs (u:t) = 
    let u = Array.to_list u in
    let rec aux = function
      | [] -> 0
      | x::u -> String.length (rs.generators.(x)) + aux u
    in aux u

  let of_string rs s : t =
    let i = ref 0 in
    let ans = ref [] in
    while !i < String.length s do
      if s.[!i] <> '(' then
        (
          ans := String.of_char s.[!i] :: !ans;
          Pervasives.incr i
        )
      else
        let j = String.index_from s !i ')' in
        ans := String.sub s (!i + 1) (j - !i - 1) :: !ans;
        i := j+1
    done;
    let ans = List.map (Array.index rs.generators) !ans in
    Array.of_list (List.rev ans)

  let of_generator g : t = [|g|]

  let sub (w : t) p q : t = Array.sub w p q
end

module W = Word

(** Operations on rules. *)
module Rule = struct
  type t = rule

  let source rs r =
    fst (IMap.find r rs.rules)

  let target rs r =
    snd (IMap.find r rs.rules)
end

(** A rule in context. *)
module CRule = struct
  type t = word * rule * word

  let to_string rs cr =
    let u,r,v = cr in
    Printf.sprintf "--%s%s%s-->" (W.to_string rs u) (string_of_rule r) (W.to_string rs v)

  (** Source of a crule. *)
  let source rs cr =
    let u,r,v = cr in
    let s = Rule.source rs r in
    W.concat [u; s; v]

  (** Target of a crule. *)
  let target rs cr =
    let u,r,v = cr in
    let t = Rule.target rs r in
    W.concat [u; t; v]

  let context (u,r,v) (w,w') =
    let u = Array.append w u in
    let v = Array.append v w' in
    (u,r,v)
end

(** A sequence of rules in context. *)
module CRules = struct
  type t = CRule.t list

  let to_string rs r =
    let rr =
      List.map
        (fun cr ->
          CRule.to_string rs cr
	  ^" "
          ^W.to_string rs (CRule.target rs cr)
        ) r
    in
    (* TODO: should we store the target in crules for indentities (normalize would
       then produce a crule)? *)
    if r = [] then "" else
      W.to_string rs (CRule.source rs (List.hd r))
      ^" "
      ^String.concat " " rr

  let context r c =
    List.map (fun r -> CRule.context r c) r

  let cons (r:CRule.t) (rr:t) : t =
    r::rr

  let source rs (r:t) =
    CRule.source rs (List.hd r)

  let target rs (r:t) =
    CRule.target rs (List.last r)
end

(** Create an empty presentation. *)
let create () =
  {
    generators = [||];
    nrules = 0;
    rules = IMap.empty;
    (*equations = [];*)
  }

(** Number of generators in a presentation. *)
let nb_generators rs =
  Array.length rs.generators

(** Number of rules in a presentation. *)
let nb_rules rs =
  IMap.cardinal rs.rules

(*let nb_equations rs = 
  List.length rs.equations*)

(** Ensure that a word is valid in a given presentation. *)
let is_word rs (w:word) =
  Array.for_all (fun a -> a < nb_generators rs) w

(** Check whether a presentation contains a generator with given name. *)
let has_generator rs w =
  Array.contains rs.generators w

(** Add a new generator. *)
let add_generator ?name rs =
  let name =
    match name with
    | Some name -> name
    | None ->
      String.of_char (char_of_int (nb_generators rs + int_of_char 'a'))
  in
  { rs with generators = Array.append rs.generators [|name|] }

(** Add generators. *)
let add_generators rs n =
  let rs = ref rs in
  for i = 0 to n - 1 do
    rs := add_generator !rs
  done;
  !rs

let add_rule ?(dup=true) rs ((r1,r2) as r) =
  assert (is_word rs r1);
  assert (is_word rs r2);
  if (not dup) && IMap.exists (fun _ (u,v) -> u = r1 && v = r2) rs.rules then
    rs
  else
    {
     generators = rs.generators;
     nrules = rs.nrules+1;
     rules = IMap.add rs.nrules r rs.rules;
(* equations = normaliser les équations existantes ? ajouter les nouvelles paires critiques (normalisées) ? *)
   }

let rec add_rules ?(dup=true) rs = function
  | [] -> rs
  | r :: rr -> add_rules ~dup (add_rule ~dup rs r) rr
	
let rm_rule rs r =
  { rs with rules = IMap.remove r rs.rules }

(** Orient rules according to partial order. *)
let orient rs leq =
  let rules = IMap.map (fun (l,r) -> if leq r l then (l,r) else (r,l)) rs.rules in
  { rs with rules = rules }

(** String representation of a presentation. *)
let to_string rs =
  let generators = String.concat "," (Array.to_list rs.generators) in
  let rules = ref [] in
  IMap.iter
    (fun r (r1,r2) ->
      rules := (string_of_rule r^" : "^W.to_string rs r1^" -> "^W.to_string rs r2) :: !rules
    ) rs.rules;
  let rules = List.rev !rules in
  let rules = String.concat ", " rules in
  if nb_generators rs <= 0 then "empty" else
    Printf.sprintf "%s | %s" generators rules

(******************* ORDERS ******************)

(** deglex order. *)
let deglex ?(co=false) lex rs (u:word) (v:word) =
  let lu = Array.length u in
  let lv = Array.length v in
  if lu < lv then true
  else if lu > lv then false
  else
    if not co then
      (
        let i = ref 0 in
        while !i < lu && u.(!i) = v.(!i) do incr i done;
        if !i = lu then false else lex rs.generators.(u.(!i)) rs.generators.(v.(!i))
      )
    else
      (
        let i = ref (lu-1) in
        while !i >= 0 && u.(!i) = v.(!i) do decr i done;
        if !i < 0 then false else lex rs.generators.(u.(!i)) rs.generators.(v.(!i))
      )

(** lexicographic order. **)
let lexico lex rs (u:word) (v:word) =
  let lu = Array.length u in
  let lv = Array.length v in
  let l = min lu lv in
  let i = ref 0 in
  while !i < l && u.(!i) = v.(!i) do incr i done;
  if !i = lu then true else if !i = lv then false else lex rs.generators.(u.(!i)) rs.generators.(v.(!i))

let lablex ?(rev=false) rs (u:word) (v:word) =
  let lu = Array.length u in
  let lv = Array.length v in
  let u = Array.to_list u in
  let u = List.map (fun g -> rs.generators.(g)) u in
  let u = String.concat "" u in
  let v = Array.to_list v in
  let v = List.map (fun g -> rs.generators.(g)) v in
  let v = String.concat "" v in
  (u = v && lu < lv) || (if rev then u > v else u < v)

(** weighted lexicographic order. **)
let weightlex ?(rev=false) lex rs (u:word) (v:word) =
  let lu = Array.length u in
  let lv = Array.length v in 
  (lu < lv) ||
    (
      (lu = lv) && 
	(
	  let wu = Array.fold_left (fun n x  -> n + String.length (rs.generators.(x))) 0 u in
	  let wv = Array.fold_left (fun n x  -> n + String.length (rs.generators.(x))) 0 v in
	  (wu < wv) || (wu = wv && if rev then lexico lex rs v u else lexico lex rs u v)
	)
    )

(******************** NORMALISATION *******************)

(** Compute the leftmost instance of u in v. *)
let instance u v : cword option =
  let ans = ref None in
  try
    for o = 0 to W.length v - W.length u do
      if W.included o u v then
        let o2 = o + W.length u in
        ans := Some (W.sub v 0 o, u, W.sub v o2 (W.length v - o2));
        raise Exit
    done;
    raise Exit
  with
    | Exit -> !ans

(** Find a leftmost possible reduction in a word. *)
let reduction_left ?rules rs u : crule option =
  let rules = Option.default rs.rules rules in
  let ans = ref None in
  IMap.iter 
    (fun r (r1,r2) -> match instance r1 u with
      | None -> ()
      | Some (v,_,w) ->
	(
          match !ans with
            | None -> ans := Some (v,r,w)
            | Some (v',r',w') ->
              if W.length v < W.length v' then
		ans := Some (v,r,w)
	)
    ) 
    rules;
  !ans

(** Find a reduction step. *)
let reduce rules u : crule = 
  IMap.find_map
    (fun r (r1,r2) -> Option.map (fun (v,_,w) -> v,r,w) (instance r1 u))
    rules
    
(** Normalize a word. *)
let normalize ?rules rs u =
  let rules = Option.default rs.rules rules in
  let u = ref u in
  try
    while true do
      let cr = reduce rules !u in
      u := CRule.target rs cr
    done;
    assert false
  with
    | Not_found -> !u
      
(** Path witnessing the normalization of a word. *)
let normalize_path rs u : CRules.t =
  let u = ref u in
  let r = ref [] in
  try
    while true do
      let cr = reduce rs.rules !u in
      r := cr :: !r;
      u := CRule.target rs cr
    done;
    assert false
  with
    | Not_found -> List.rev !r


(********************** CANONISATION *************************)

(** Normalize right members of rules. *)
let canonize_right rs =
  let rs = ref rs in
  IMap.iter
    (fun r (r1,r2) ->
      let r2' = normalize !rs r2 in
      if r2' <> r2 then
        (
          rs := rm_rule !rs r;
          rs := add_rule !rs (r1, r2');
        )
    ) !rs.rules;
  !rs

(** Remove duplicate rules. *)
let canonize_dup rs =
  let rs = ref rs in
  IMap.iter_pairs ~reflexive:false
    (fun r (r1,r2) s (s1,s2) ->
      if r1 = s1 && r2 = s2 then
        rs := rm_rule !rs s
    ) !rs.rules;
  !rs

(** Remove left inclusions of rules. *)
let canonize_left ~lt rs =
  let f rs =
    let rs = ref rs in
    try
      IMap.iter_pairs ~symmetric:true ~reflexive:false
        (fun r (r1,r2) s (s1,s2) ->
	  try 
	    for o = 0 to Array.length r1 - Array.length s1 do
	      if Array.included o s1 r1 then
		let u = Array.sub r1 0 o in
                let v = Array.sub_right r1 0 (Array.length r1 - Array.length s1 - o) in
		let r1' = normalize !rs (W.concat [u;s2;v]) in
		rs := rm_rule !rs r;
		  (* if r1' <> r2 then rs := add_rule ~dup:false !rs (r1',r2) *)
		if r1' <> r2 && lt !rs r1' r2 then rs := add_rule ~dup:false !rs (r2,r1');
		if r1' <> r2 && lt !rs r2 r1' then rs := add_rule ~dup:false !rs (r1',r2);
		  (* We restart from the begining as soon as we changed
                     something. *)
		raise Exit
            done
	  with Not_found -> ()
	) 
	!rs.rules;
      !rs
    with
      | Exit -> !rs
  in
  fixpoint f rs

(** Put a rewriting system in canonical form. *)
let canonize ~lt rs =
  let aux rs = 
    let rs = canonize_right rs in
    let rs = canonize_dup rs in
    let rs = canonize_left ~lt rs in
    rs
  in fixpoint aux rs


(************************ CRITICAL BRANCHINGS **********************)

let rec critical_uples_in rs c d =
  let ans = ref [] in
  List.iter_pairs
    (fun cr cs ->
      let r1 = CRule.source rs (List.hd cr) in
      let s1 = CRule.source rs (List.hd cs) in
      let ostart = max 1 (Array.length r1 - Array.length s1 + 1) in
      for o = ostart to Array.length r1 - 1 do
        let l1 = o in
        let l2 = Array.length r1 - l1 in
        let l3 = Array.length s1 - l2 in
        let b =
          try
            for i = 0 to l2 - 1 do
              if s1.(i) <> r1.(i+o) then raise Exit
            done;
            true
          with
          | Exit -> false
        in
        if b then
          let w = Array.sub s1 l2 l3 in
          let cr = List.map (fun (u,r,v) -> u,r,W.append v w) cr in
          let w = Array.sub r1 0 l1 in
          let cs = List.map (fun (u,r,v) -> W.append w u,r,v) cs in
          ans := (cr@cs) :: !ans
      done
    ) c d;
  !ans

(** Compute critical uples. We suppose that there are no inclusion
    branchings. *)
let rec critical_uples ?rules rs n : crule list list =
  assert (n > 0);
  let rules = Option.default rs.rules rules in
  if n = 1 
  then IMap.fold (fun r _ l -> [W.empty,r,W.empty]::l) rules []
  else
    let c = critical_uples ~rules rs (n-1) in
    let d = critical_uples ~rules rs 1 in
    critical_uples_in rs c d

let critical_pairs ?rules rs : (crule * crule) list =
  let rules = Option.default rs.rules rules in
  let ans = ref [] in
  IMap.iter_pairs ~symmetric:true
    (fun r (r1,_) s (s1,_) ->
      let ostart = max 1 (Array.length r1 - Array.length s1 + 1) in
      for o = ostart to Array.length r1 - 1 do
        let l1 = o in
        let l2 = Array.length r1 - l1 in
        let l3 = Array.length s1 - l2 in
        let b = ref true in
        for i = 0 to l2 - 1 do
          b := !b && (s1.(i) = r1.(i+o))
        done;
        if !b then
          let cr = W.empty, r, Array.sub s1 l2 l3 in
          let cs = Array.sub r1 0 l1, s, W.empty in
          ans := (cr,cs) :: !ans
      done
    ) rules;
  !ans

(*
let critical_pairs rs =
  List.rev_map
    (function
    | [cr; cs] -> cr, cs
    | _ -> assert false)
    (critical_uples rs 2)
*)

(** Normal forms of targets of critical pairs. *)
let critical_rules ?rules lt rs =
  let rules = Option.default rs.rules rules in
  let cp = critical_pairs ~rules rs in
  let nb = List.length cp in
  let norm r = normalize ~rules rs (CRule.target rs r) in
  if nb > 500 then Lang.printf "critical branchings: 0/%i (0%%)\r%!" nb;
  let rec aux i = function
    | [] -> []
    | (l, r) :: eqs -> 
	if nb > 500 && i mod (nb/100) = 0 then 
	  Lang.printf "critical branchings: %i/%i (%i%%)\r%!" i nb (i/(nb/100));	
	let l = norm l in	
	let r = norm r in	
	if l = r then aux (i+1) eqs
	else if lt rs r l then (l, r) :: (aux (i+1) eqs) else (r, l) :: (aux (i+1) eqs)
  in
  let eqs = aux 1 cp in 
  let eqs = List.remove_duplicates eqs in
  let eqs = List.sort 
    (fun (l, r) (l', r') -> if lt rs l l' then -1 else 1) 
    eqs 
  in eqs

let cocritical_pairs rs =
  let ans = ref [] in
  IMap.iter_pairs ~symmetric:true
    (fun r (_,r1) s (_,s1) ->
      let ostart = max 1 (Array.length r1 - Array.length s1 + 1) in
      for o = ostart to Array.length r1 - 1 do
        let l1 = o in
        let l2 = Array.length r1 - l1 in
        let l3 = Array.length s1 - l2 in
        let b = ref true in
        for i = 0 to l2 - 1 do
          b := !b && (s1.(i) = r1.(i+o))
        done;
        if !b then
          let cr = W.empty, r, Array.sub s1 l2 l3 in
          let cs = Array.sub r1 0 l1, s, W.empty in
          ans := (cr,cs) :: !ans
      done
    ) rs.rules;
  !ans

let cocritical_rules rs =
  let cp = cocritical_pairs rs in
  let f r = CRule.source rs r in
  List.rev_map (fun (l,r) -> f l, f r) cp


(********************************* COMPLETION **********************************)

(** Raised by lt when rule should not be oriented in completion. *)
exception Cannot_compare

let completion_step ?rules ~lt rs =
  let rules = Option.default rs.rules rules in
  let cp = critical_pairs ~rules rs in
  let rs = ref rs in
  let ncp = List.length cp in
  List.iteri
    (fun i (cr,cs) ->
      if ncp > 500 && i mod (ncp/100) = 0 then Printf.printf "completing: %i/%i (%i%%)\r%!" i ncp (i/(ncp/100));
      let r2 = CRule.target !rs cr in
      let s2 = CRule.target !rs cs in
      let r2' = normalize ~rules !rs r2 in
      let s2' = normalize ~rules !rs s2 in
      if r2' = s2' then ()
      else if lt !rs r2' s2' then rs := add_rule !rs ~dup:false (s2', r2')
	  else if lt !rs s2' r2' then rs := add_rule !rs ~dup:false (r2', s2')
	  else raise Cannot_compare
    ) cp;
  !rs

(** Perform a Knuth-Bendix completion. *)
(* TODO: avoid computing all critical pairs at each step by using
   critical_uples_in. *)
let completion ~lt rs =
  let i = ref 0 in
  let f rs =
    let n = nb_rules rs in
    if n >= 100 then Printf.printf "step: %d, rules: %d...\n%!" !i n;
    incr i;
    completion_step ~lt rs
  in
  fixpoint f rs

let canonized_completion ~lt rs =
  let f rs = completion_step ~lt (canonize ~lt rs) in
  let f =
    let i = ref 0 in
    fun rs ->
      incr i;
      let n = nb_rules rs in
      if n >= 100 then Printf.printf "step: %d, rules: %d...\n%!" !i n;
      f rs
  in
  fixpoint f rs


(******************************** EXPERIMENTS *********************************)

let rules_sw rs =
  let rules =
    let ans = ref [] in
    IMap.iter
      (fun _ r ->
        ans := r :: !ans
      ) rs.rules;
    !ans
  in
  let left = List.rev_map fst rules in
  (* let right = List.rev_map snd rules in *)
  (* let w = left@right in *)
  let w = left in
  let w = List.map (W.to_string rs) w in
  let w = List.map String.substrings w in
  let w = List.concat w in
  let w = List.remove_duplicates w in
  let w = List.filter (fun w -> String.length w > 1) w in
  w

(** Fonctions sur les équations **)
(* Normalisation des équations *)
let rec equations_normalize ~lt rs = function
  | [] -> []
  | (u, v) :: eqs ->
    let u' = normalize rs u in
    let v' = normalize rs v in
    let eqs' = equations_normalize ~lt rs eqs in
    if u' = v' then eqs' else
      (if lt rs v' u' then (u', v') else (v', u'))::eqs'

(* Paires critiques -> Équations *)
let rec equations_of_cps ~lt rs = function
  | [] -> []
  | (cr, cs) :: cps ->
    let u = CRule.target rs cr in
    let v = CRule.target rs cs in
    (u, v) :: equations_of_cps ~lt rs cps

(* Tri des équations *)
let equations_sort ~lt rs eqs =
  List.sort (fun (u, v) (u', v') -> if lt rs u u' then -1 else 1) eqs

(* Affichage d'une équation *)
let equation_string rs (u, v) =
  Printf.sprintf "%s = %s" (Word.to_string rs u) (Word.to_string rs v)

(** Décomposition du calcul des paires critiques **)
(* Paires critiques entre r et s *)
let critical_pairs_one_one r (r1, r2) s (s1, s2) =
  let ans = ref [] in
  let ostart = max 1 (Array.length r1 - Array.length s1 + 1) in
  for o = ostart to Array.length r1 - 1 do
    let l1 = o in
    let l2 = Array.length r1 - l1 in
    let l3 = Array.length s1 - l2 in
    let b = ref true in
    for i = 0 to l2 - 1 do
      b := !b && (s1.(i) = r1.(i+o))
    done;
    if !b then
      let cr = W.empty, r, Array.sub s1 l2 l3 in
      let cs = Array.sub r1 0 l1, s, W.empty in
      ans := (cr,cs) :: !ans
  done;
  !ans

(* Paires critiques entre r et le reste des règles *)
let critical_pairs_one r (r1, r2) rules =
  let ans = ref [] in
  IMap.iter
    (fun s (s1, s2) -> ans := List.append (critical_pairs_one_one r (r1, r2) s (s1, s2)) !ans)
    rules;
  IMap.iter
    (fun s (s1, s2) ->
      if r <> s then ans := List.append (critical_pairs_one_one s (s1, s2) r (r1, r2)) !ans
    )
    rules;
  !ans

(** Complétion règle par règle : pas efficace **)
let completion_one ~lt rs =
  let rs = canonize ~lt rs in
  let cp = critical_pairs rs in
  let equations = equations_sort ~lt rs (equations_normalize ~lt rs (equations_of_cps ~lt rs cp)) in
  let rec aux n rs = function
    | [] -> rs
    | (u, v) :: eqs ->
      let r = rs.nrules in
      let rs = canonize ~lt { rs with nrules = r + 1 ; rules = IMap.add r (u, v) rs.rules } in
      let eqs1 = equations_normalize ~lt rs eqs in
      let eqs2 = equations_normalize ~lt rs (equations_of_cps ~lt rs (critical_pairs_one r (u, v) rs.rules)) in
      let eqs =
        if n mod 10 = 0
        then equations_sort ~lt rs (List.append eqs1 eqs2)
        else List.append eqs1 eqs2
      in
      if n mod 10 = 0 then
        (
          Printf.printf "Step %i :\n %i rules - last one : %s\n %i equations remaining\n"
            n (rs.nrules) (equation_string rs (u, v)) (List.length eqs) ;
          flush stdout
        );
      aux (n+1) rs eqs
  in
  aux 1 rs equations
  
(** Ajout des n premières paires critiques non confluentes **)
let addncp ~lt rs n =
  let eqs = critical_rules lt rs in
  let eqs = List.first_n_elts n eqs in
  let rs = add_rules rs eqs in
  canonize ~lt rs

(** Homotopy generator corresponding to a branching. *)
let cp_hgen ?(sort=true) rs (r1,r2) =
  (* Printf.printf "cp_hgen: %s / %s\n%!" (CRule.to_string rs r1) (CRule.to_string rs r2); *)
  let w1 = CRule.target rs r1 in
  let w2 = CRule.target rs r2 in
  let r1' = normalize_path rs w1 in
  let w' = CRules.target rs r1' in
  let r2' = normalize_path rs w2 in
  let w'' = CRules.target rs r2' in
  assert (w' = w'');
  (* Printf.printf "cp_hgen residuals: %s / %s\n%!" (CRules.to_string rs r1') (CRules.to_string rs r2'); *)
  let hgen = r1::r1', r2::r2' in
  if sort then
    sort_pair hgen
  else
    hgen

(** Compute an homotopy basis on a rewriting system which is supposed to be
    convergent and reduced. *)
let hbasis rs =
  let cp = critical_pairs rs in
  let hbasis = ref [] in
  List.iter
    (fun (r1,r2) ->
      let hgen = cp_hgen rs (r1,r2) in
      if not (List.mem hgen !hbasis) then hbasis := hgen :: !hbasis
    ) cp;
  !hbasis

let crules_normalize rs r =
  let w = CRules.target rs r in
  let r' = normalize_path rs w in
  r@r'

let reduced_hbasis rs =
  let hbasis = hbasis rs in
  let hbasis = Array.of_list hbasis in
  let nhb = Array.length hbasis in
  let hremoved = Array.make nhb false in
  let ct = critical_uples rs 3 in
  let ct = List.map (function [r1;r2;r3] -> (r1,r2,r3) | _ -> assert false) ct in
  let cm_create () =
    let counter = Array.make nhb 0 in
    let moustache = Array.make nhb false in
    counter, moustache
  in
  (* r1 and r2 and two coinitial paths. We compute the number of occurrences of
     each homotopy generator, and whether it occurs with a moustache. *)
  let count cm ((r1 : crule list), (r2 : crule list)) =
    (* let r1 = if r1 = [] then [] else crules_normalize rs r1 in *)
    (* let r2 = if r2 = [] then [] else crules_normalize rs r2 in *)
    (* Printf.printf "\n\n\n****count\n%!"; *)
    (* Printf.printf "r1: %s\n%!" (CRules.to_string rs r1); *)
    (* Printf.printf "r2: %s\n%!" (CRules.to_string rs r2); *)
    if r1 <> [] && r2 <> [] then assert (CRules.source rs r1 = CRules.source rs r2);
    let counter, moustache = cm in
    let rec aux (r1:crule list) (r2:crule list) =
      (* Printf.printf "aux\n%!"; *)
      (* Printf.printf "r1: %s\n%!" (CRules.to_string rs r1); *)
      (* Printf.printf "r2: %s\n%!" (CRules.to_string rs r2); *)
      if r1 <> [] && r2 <> [] then
        assert (CRules.source rs r1 = CRules.source rs r2);
      (* let aux r1 r2 = *)
      (* let f,g = aux r1 r2 in *)
      (* Printf.printf "aux\n%!"; *)
      (* Printf.printf "r1: %s\n%!" (CRules.to_string rs r1); *)
      (* Printf.printf "r2: %s\n%!" (CRules.to_string rs r2); *)
      (* Printf.printf "is\n%!"; *)
      (* Printf.printf "f: %s\n%!" (CRules.to_string rs f); *)
      (* Printf.printf "g: %s\n%!" (CRules.to_string rs g); *)
      (* f,g *)
      (* in *)
      match r1, r2 with
      | [], _ -> r2, []
      | _, [] -> [], r1
      | r1::r1', r2::r2' when r1 = r2 -> aux r1' r2'
      | r1::r1', r2::r2' ->
        let w1,r1,w1' = r1 in
        let w2,r2,w2' = r2 in
        (* Do we have a moustache? *)
        let m = (not (W.is_empty w1) && not (W.is_empty w2)) || (not (W.is_empty w1') && not (W.is_empty w2')) in
        let w,w1,w2 =
          if Array.length w1 <= Array.length w2 then
            let w = w1 in
            let lw = Array.length w in
            assert (Array.is_prefix w w2);
            let w2 = Array.sub w2 lw (Array.length w2 - lw) in
            w, [||], w2
          else
            let w = w2 in
            let lw = Array.length w in
            assert (Array.is_prefix w w1);
            let w1 = Array.sub w1 lw (Array.length w1 - lw) in
            w, w1, [||]
        in
        let w',w1',w2' =
          if Array.length w1' <= Array.length w2' then
            let w' = w1' in
            let lw' = Array.length w1' in
            assert (Array.is_suffix w' w2');
            let w2' = Array.sub w2' 0 (Array.length w2' - lw') in
            w', [||], w2'
          else
            let w' = w2' in
            let lw'= Array.length w2' in
            assert (Array.is_suffix w' w1');
            let w1' = Array.sub w1' 0 (Array.length w1' - lw') in
            w', w1', [||]
        in
        let peiffer =
          if w1 = [||] then
            (
              assert (w2' = [||]);
              W.length (Rule.source rs r1) <= W.length w2 && W.length (Rule.source rs r2) <= W.length w1'
            )
          else
            (
              assert (w1' = [||]);
              assert (w2 = [||]);
              W.length (Rule.source rs r1) <= W.length w2' && W.length (Rule.source rs r2) <= W.length w1
            )
        in
        let f,g =
          if peiffer then
            (
              if w1 = [||] then
                let l2 = W.length (Rule.source rs r2) in
                let w = W.sub w1' 0 (W.length w1' - l2) in
                [W.empty,r1,W.append w (Rule.source rs r2); W.append (Rule.target rs r1) w,r2,W.empty],
                [W.append (Rule.source rs r1) w,r2,W.empty; W.empty,r1,W.append w (Rule.target rs r2)]
              else
                let l1 = W.length (Rule.source rs r1) in
                let w = W.sub w2' 0 (W.length w2' - l1) in
                assert (w2 = [||]);
                [W.append (Rule.source rs r2) w,r1,W.empty; W.empty,r2,W.append w (Rule.target rs r1)],
                [W.empty,r2,W.append w (Rule.source rs r1); W.append (Rule.target rs r2) w,r1,W.empty]
            )
          else
            cp_hgen ~sort:false rs ((w1,r1,w1'), (w2,r2,w2'))
        in
        let hgen = sort_pair (f,g) in
        let f = List.tl f in
        let g = List.tl g in
        let f = CRules.context f (w,w') in
        let g = CRules.context g (w,w') in
        (* if peiffer then Printf.printf "peiffer!\n%!"; *)
        (* if m then Printf.printf "moustache!\n%!"; *)
        if not peiffer then
          (
            let nhgen =
              try
                Array.index hbasis hgen
              with
              | Not_found ->
                let f, g = hgen in
                failwith (Printf.sprintf "index of generator not found:\n%s\n%s\n%!" (CRules.to_string rs f) (CRules.to_string rs g))
            in
            moustache.(nhgen) <- moustache.(nhgen) || m;
            Array.incr counter nhgen;
          );
        let r1'',f' = aux r1' f in
        let g',r2'' = aux g r2' in
        let r1''',r2''' = aux f' g' in
        r1''@r1''', r2''@r2'''
    in
    let f,g = aux r1 r2 in
    (* Printf.printf "count answer\n%!"; *)
    (* Printf.printf "f: %s\n%!" (CRules.to_string rs f); *)
    (* Printf.printf "g: %s\n%!" (CRules.to_string rs g); *)
    f,g
  in
  let ctlen = List.length ct in
  let ctcur = ref 0 in
  List.iter
    (fun (r1,r2,r3) ->
      (* Printf.printf "r1: %s\n%!" (CRule.to_string rs r1); *)
      (* Printf.printf "r2: %s\n%!" (CRule.to_string rs r2); *)
      (* Printf.printf "r3: %s\n%!" (CRule.to_string rs r3); *)
      (* First face *)
      (* Printf.printf "First face\n%!"; *)
      let cm_left = cm_create () in
      let f1, g1 = count cm_left ([r1],[r2]) in
      let f2, g2 = count cm_left ([r2],[r3]) in
      let n1 = normalize_path rs (CRules.target rs (r1::f1)) in
      let n2 = normalize_path rs (CRules.target rs (r3::g2)) in
      let e,e' = count cm_left (g1@n1,f2@n2) in
      assert (e = []);
      assert (e' = []);
      (* Second face *)
      (* Printf.printf "Second face\n%!"; *)
      let cm_right = cm_create () in
      let f, g = count cm_right ([r1],[r3]) in
      let e, f' = count cm_right (f1@n1,f) in
      assert (e = []);
      let g', e = count cm_right (g,g2@n2) in
      assert (e = []);
      let e, e' = count cm_right (f',g') in
      assert (e = [] && e' = []);

      let dep = Poset.create nhb in
      let cl, ml = cm_left in
      let cr, mr = cm_right in
      (
        try
          Printf.printf "Homotopy reduction: %d%%\r%!" (!ctcur*100/ctlen);
          incr ctcur;
          for i = 0 to nhb - 1 do
            if not hremoved.(i) && not (ml.(i) || mr.(i)) && (cl.(i) + cr.(i) = 1) then
              (
                if Int.for_all (fun j -> i = j || cl.(j) + cl.(j) = 0 || not (Poset.le dep j i)) nhb then
                  (
                    Int.iter (fun j -> if j <> i && cl.(j) + cr.(j) <> 0 then Poset.add dep i j) nhb;
                    hremoved.(i) <- true;
                    let f,g = hbasis.(i) in
                    Printf.printf "\nWe remove:\n%s\n%s\n" (CRules.to_string rs f) (CRules.to_string rs g);
                    Printf.printf "with\n%s\n%s\n%s\n\n%!" (CRule.to_string rs r1) (CRule.to_string rs r2) (CRule.to_string rs r3);
                    for i = 0 to nhb - 1 do
                      let c = cl.(i) + cr.(i) in
                      if c <> 0 then Printf.printf "α%d%s : %d, " i (if ml.(i) || mr.(i) then "*" else "") c
                    done;
                    Printf.printf "\n%!";
                    (raise Exit : unit)
                  )
                else
                  Printf.printf "Cyclic substitution skipped.\n\n%!"
              )
          done
        with Exit -> ()
      )
    ) ct;
  let ans = ref [] in
  for i = 0 to nhb - 1 do
    if not hremoved.(i) then
      ans := hbasis.(i) :: !ans
  done;
  List.rev !ans
