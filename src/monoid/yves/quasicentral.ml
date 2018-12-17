(** Test quasicentral elements. *)

open Standard
open FreeMonoid

(** Éléments localement quasi-centraux - test **)
let cell_tail u =
  Array.of_list (List.tl (Array.to_list u))

let rec eqs_tails = function
  | [] -> []
  | (u, v) :: eqs ->
    let tails = eqs_tails eqs in
    (*let tails =
      if Array.length v > 1
      then (cell_tail v) :: tails
      else tails
      in*)
    let tails =
      if Array.length u > 2 then
        (cell_tail u) :: tails
      else
        tails
    in
    tails

let rec left_products rs u = function
  | [] -> []
  | x :: gens ->
    let u' = normalize rs (Array.append x u) in
    u' :: left_products rs u gens

let rec right_products rs u = function
  | [] -> []
  | x :: gens ->
    let u' = normalize rs (Array.append u x) in
    u' :: right_products rs u gens

let is_quasicentral rs u =
  let gens = List.map (Word.of_string rs) (Array.to_list rs.generators) in
  let left = left_products rs u gens in
  let right = right_products rs u gens in
(*    Printf.printf "Element : %s\n" (Word.to_string rs u);
    Printf.printf "  Left-products :" ;
    List.iter (fun v -> Printf.printf " %s" (Word.to_string rs v)) left ;
    Printf.printf "\n  Right-products :" ;
    List.iter (fun v -> Printf.printf " %s" (Word.to_string rs v)) right ;*)
    let test =  List.exists (fun x -> List.mem x right) left
    in
(*      Printf.printf "\n Quasi-central : %b\n" test ; flush stdout ;*)
      test

let rec cohead = function
  | [] -> failwith "cohead"
  | x :: [] -> x
  | x :: xx -> cohead xx

let rec cotail = function
  | [] -> failwith "cotail"
  | x :: [] -> []
  | x :: xx -> x :: cotail xx

(* Ajouts des éléments quasi-centraux *)
let rec add_quasicentral_elements rs origens = function
  | [] -> rs
  | (u, v) :: eqs ->
    let gens = List.map (Word.of_string rs) (Array.to_list rs.generators) in
    let add = [] in
    let add =
      if Array.length u > 1 && Array.length v > 1
      then
        let u = Word.of_string rs
          (String.concat "" (List.map (fun g -> rs.generators.(g)) (Array.to_list u))) in
        let v = Word.of_string rs
          (String.concat "" (List.map (fun g -> rs.generators.(g)) (Array.to_list v))) in
        if u = v then u :: add else add
      else add
    in
    let add =
      if Array.length u > 2 && Array.length v > 2
      then
        let x = Array.of_list [List.hd (Array.to_list u)] in
        let u' = Array.of_list (List.tl (Array.to_list u)) in
        let v' = Array.of_list (cotail (Array.to_list v)) in
        let y = Array.of_list [cohead (Array.to_list v)] in
        if u' = v' && List.mem x origens && List.mem y origens then u' :: add
        else
          let u' = Array.of_list (cotail (Array.to_list u)) in
          let x = Array.of_list [cohead (Array.to_list u)] in
          let y = Array.of_list [List.hd (Array.to_list v)] in
          let v' = Array.of_list (List.tl (Array.to_list v)) in
          if u' = v' && List.mem x origens && List.mem y origens then u' :: add else add
      else add
    in
    let add =
      if Array.length u = 2 && Array.length v = 2
      then
        let x = Array.of_list (cotail (Array.to_list u)) in
        let x' = Array.of_list (List.tl (Array.to_list u)) in
        let y = Array.of_list (cotail (Array.to_list v)) in
        let y' = Array.of_list (List.tl (Array.to_list v)) in
        if List.mem x origens && List.mem y origens && x = y' && x' = y
        then v :: add else add
      else add
    in
    let rec aux rs tempgens = function
      | [] -> add_quasicentral_elements rs origens eqs
      | u :: uu ->
        if not (List.mem u tempgens)
          && List.for_all (fun x -> List.mem [|x|] origens) (Array.to_list u)
        then
          let rs = add_generator rs ~name:(Word.to_string rs u) in
          let tempgens = u :: gens in
          let tgt = Word.of_generator ((nb_generators rs) - 1) in
          let rs = add_rule rs (u, tgt) in
          Printf.printf "+ %s\n" (Word.to_string rs u) ;
          aux rs tempgens uu
        else aux rs tempgens uu
    in aux rs gens add

(*
        if Array.length u > 2
        then
          let u' = Array.of_list (List.tl (Array.to_list u)) in
            if List.mem u' gens
            then (rs, gens)
            else
              let left =  left_products rs u' gens in
              let right = right_products rs u' gens in
                if List.exists (fun x -> List.mem x right) left
                then
                  let rs = add_generator rs ~name:(Word.to_string rs u') in
                  let gens = gens @ [u'] in
                  let tgt = Word.of_generator ((nb_generators rs) - 1) in
                  let rs = add_rule rs (u', tgt) in
                    Printf.printf "+ %s\n" (Word.to_string rs u') ;
                    (rs, gens)
                else (rs, gens)
        else (rs, gens)
      in add_quasicentral_elements rs gens eqs
 *)

let add_qc rs gens =
  let eqrules = IMap.to_list rs.rules in
  add_quasicentral_elements rs gens eqrules

let () =
  LangMonoid.register "qc" "Add locally-quasi-central elements." 0
    (fun rs a -> 
      let gens = List.map 
        (Word.of_string rs) 
        (List.filter (fun x -> String.length x = 1) (Array.to_list rs.generators))
      in
      add_qc rs gens
    );
  LangMonoid.register "kbsqc" "One step of canonized Knuth-Bendix completion with generator adjunction." 0
    (fun rs a ->
      let lt = LangMonoid.lt in
      let gens = List.map 
        (Word.of_string rs) 
        (List.filter (fun x -> String.length x = 1) (Array.to_list rs.generators))
      in
      canonize ~lt
        (completion_step ~lt
	   (canonize ~lt 
	      (add_qc (canonize ~lt rs) gens)
	   )
        )
    )

(**
   Test complétion :
   - ajoute les éléments localement quasi-centraux des règles comme générateurs,
   - calcule les paires critiques et les normalise, ajoute les équations obtenues comme règles
   - calcule les nouvelles paires critiques, trie les relations obtenues.
**)
  let completion_test ~lt rs =
    let gens = List.map (Word.of_string rs) (Array.to_list rs.generators) in
    let rs = canonize ~lt (add_qc (canonize ~lt rs) gens) in
    let cp = critical_pairs rs in
    let equations =
      equations_sort ~lt rs (equations_normalize ~lt rs (equations_of_cps ~lt rs cp))
    in
  (*  let tails = eqs_tails equations in
      let quasicentral_elems = List.filter (is_quasicentral rs) tails in
      List.iter (fun u -> Printf.printf "Quasi-central: %s\n" (Word.to_string rs u)) quasicentral_elems ;*)
    let rec aux n rs cps = function
      | [] ->
         if cps = [] then canonize ~lt rs
         else
           let eqs = equations_of_cps ~lt rs cps in
           let rs = canonize ~lt (add_qc (canonize ~lt rs) gens) in
           let eqs = equations_sort ~lt rs (equations_normalize ~lt rs eqs) in
           Printf.printf
             "Step %i : %i rules - %i equations remaining\n" n (rs.nrules) (List.length eqs) ;
           flush stdout ;
           aux (n+1) rs [] eqs
      | (u, v) :: eqs ->
         let r = rs.nrules in
         let rs = { rs with nrules = rs.nrules + 1 ; rules = IMap.add rs.nrules (u, v) rs.rules ; } in
         let cps = List.append cps (critical_pairs_one r (u, v) rs.rules) in
         let eqs = equations_normalize ~lt rs eqs in
         aux n rs cps eqs
    in
    aux 1 rs [] equations

    
let () =
  LangMonoid.register "kbtest" "(Test) Canonized Knuth-Bendix completion." 0
    (fun rs a -> completion_test ~lt:LangMonoid.lt rs)

(* Test completion kbqc *)
let canonized_completion_qc ~lt rs =
  let gens = List.map (Word.of_string rs) (Array.to_list rs.generators) in
  let f rs = completion_step ~lt (canonize ~lt (add_qc (canonize ~lt rs) gens)) in
  let f =
    let i = ref 0 in
    fun rs ->
      incr i;
      let n = nb_rules rs in
      if n >= 100 then Printf.printf "step: %d, rules: %d...\n%!" !i n;
      f rs
  in
  fixpoint f rs

let () =
  LangMonoid.register "kbqc" "Canonized Knuth-Bendix completion with generator adjunction." 0
    (fun rs a ->  canonized_completion_qc ~lt:LangMonoid.lt rs)


(******************************************************************************)
(******************************************************************************)
(******************************************************************************)

(** Nouvel essai sur les éléments localement quasicentraux **)
let relation_length (u, v) = max (Array.length u) (Array.length v)

let max_relations_length rs =
  let rec aux n = function
    | [] -> n
    | (u, v) :: eqs ->
        let p = relation_length (u,v) in
          aux (max n p) eqs
  in
    aux 0 (IMap.to_list rs.rules)

let generators_of_word u =
  let rec aux = function
    | [] -> []
    | x :: gens -> x :: aux (List.filter (fun y -> y <> x) gens)
  in
  aux (Array.to_list u)

let indecomposables rs =
  let ans = ref [] in
  for i = 0 to Array.length rs.generators - 1 do
    let x = rs.generators.(i) in
    if String.length x = 1 then ans := i :: !ans
  done;
  !ans

(* let rec words_with_length generators = function *)
  (* | 0 -> [] *)
  (* | 1 -> List.map (fun x -> [|x|]) generators *)
  (* | n -> *)
    (* let words = words_with_length generators (n-1) in *)
    (* List.concat (List.map (fun x -> List.map (fun u -> Array.append [|x|] u) words) generators) *)

(* TODO: is this normal that we rule out the empty word? *)
let rec words_with_max_length generators n =
(*
  match n with
  | 0 -> []
  | n -> words_with_max_length generators (n-1) @ words_with_length generators n
*)
  if n = 0 then [] else
    let generators = List.map (fun x -> [|x|]) generators in
    let last = ref generators in
    let ans = ref [] in
    for i = 2 to n-1 do
      ans := List.rev_append !last !ans;
      let prev = !last in
      last := [];
      List.iter (fun x -> List.iter (fun u -> last := (Array.append x u) :: !last) prev) generators
    done;
    List.rev_append !last !ans

(*
      let tails = words_with_length rs generators (n-1) in
        Printf.printf "  %i: %s\n%!" n (String.concat " " (List.map (Word.to_string rs) tails));
      let rec aux words = function
        | [] -> words
        | x :: gens ->
            (List.map (fun u -> Array.append x u) tails)
            @ (aux words gens)
      in aux [] generators
 let rec words_with_max_length rs generators = function
  | 0 -> []
  | n -> words_with_max_length rs generators (n-1) @ words_with_length rs generators n
 *)

let left_products ~lt rs u =
(*
  let rec aux = function
    | [] -> []
    | x :: xx ->
      let _, xu = normalize rs (Array.append [|x|] u) in
      xu :: aux xx
  in
  List.sort
    (fun v w -> if lt rs v w then -1 else 1)
    (aux (generators_of_word u))
*)
  let ans = ref [] in
  List.iter
    (fun x ->
      let xu = normalize rs (Array.append [|x|] u) in
      ans := xu :: !ans
    ) (generators_of_word u);
  List.sort (fun v w -> if lt rs v w then -1 else 1) !ans

let right_products ~lt rs u =
  (*
  let rec aux = function
    | [] -> []
    | x :: xx ->
      let _, ux = normalize rs (Array.append u [|x|]) in
      ux :: aux xx
  in
  List.sort
    (fun v w -> if lt rs v w then -1 else 1)
    (aux (generators_of_word u))
  *)
  let ans = ref [] in
  List.iter
    (fun x ->
      let ux = normalize rs (Array.append u [|x|]) in
      ans := ux :: !ans
    ) (generators_of_word u);
  List.sort (fun v w -> if lt rs v w then -1 else 1) !ans

let is_lqc ~lt rs u =
  left_products ~lt rs u = right_products ~lt rs u

let lqc_elements ~lt rs =
  let gens = indecomposables rs in
  (* Printf.printf "Indecomposables: %s\n%!"  (String.concat " " (List.map
     (Word.to_string rs) gens)) ;*)
  let n = max_relations_length rs in
  Printf.printf "compute words of length <= %d on %d generators... %!" n (List.length gens);
  let words = words_with_max_length gens n in
  Printf.printf "done\n%!";
  let words = List.filter (fun u -> is_lqc ~lt rs u) words in
  let words = List.map
    (fun u ->
      let u = normalize rs u in
      let u = Array.to_list u in
      let u = List.map (fun x -> rs.generators.(x)) u in
      String.concat "" u
    )
    words
  in
  List.map (Word.of_string rs) words

(** Tests whether u is included in v and other elements of v are in the set x of
    generators. *)
let test_yves gens u v =
  let lu = W.length u in
  let lv = W.length v in
  try
    if lu > lv then
      false
    else
      (
        for o = 0 to lv - lu do
          try
          let ans = ref true in
          for i = 0 to lu - 1 do
            if u.(i) <> v.(i+o) then raise Not_found
          done;
          for i = 0 to o - 1 do
            if not (List.mem v.(i) gens) then raise Not_found
          done;
          for i = lu + o to lv - 1 do
            if not (List.mem v.(i) gens) then raise Not_found
          done;
          if !ans then raise Exit
          with
          | Not_found -> ()
        done;
        false
      )
  with
  | Exit -> true

let rec lqc_add rs = function
  | [] -> rs
  | u :: uu ->
    (* if Array.length u = 1 then lqc_add rs uu else *)
    if Array.exists
      (fun v ->
        let v = Word.of_string rs v in
        let gens = generators_of_word v in
        test_yves gens v u
      )
      rs.generators
    then lqc_add rs uu
    else
      let src = String.concat "" (List.map (fun x -> rs.generators.(x)) (Array.to_list u)) in
      let rs = add_generator rs ~name:src in
      let tgt = Word.of_generator ((nb_generators rs) - 1) in
      let rs = add_rule rs (u, tgt) in
      Printf.printf "+ %s\n" (Word.to_string rs u) ;
      lqc_add rs uu

let () =
  LangMonoid.register "lqc" "Computes locally quasicentral elements (up to the length of the relations)." 0
    (fun rs a -> 
      let lqcs = lqc_elements ~lt:LangMonoid.lt rs in 
      let string = String.concat ", " 
        (List.map (Word.to_string rs) lqcs)
      in 
      Printf.printf "Locally quasicentral elements: %s\n%!" string;
      rs
    );
  LangMonoid.register "addlqc" "Adds locally quasicentral elements (up to the length of the relations)." 0
    (fun rs a ->
      let lqcs = lqc_elements ~lt:LangMonoid.lt rs in 
      lqc_add rs lqcs
    )

let canonized_completion_lqc ~lt rs =
  let f rs =
    let rs = canonize ~lt rs in
    let lqcs = lqc_elements ~lt rs in
    let rs = lqc_add rs lqcs in
    let rs = canonize ~lt rs in
    let rs = completion_step ~lt rs in
    rs
  in
  let f =
    let i = ref 0 in
    fun rs ->
      incr i;
      let n = nb_rules rs in
      if n >= 100 then Printf.printf "step: %d, rules: %d...\n%!" !i n;
      f rs
  in
  fixpoint f rs

let () =
  LangMonoid.register "kblqc" "(Better) canonized Knuth-Bendix completion with generator adjunction." 0
    (fun rs a -> 
      canonized_completion_lqc ~lt:LangMonoid.lt rs
    )
