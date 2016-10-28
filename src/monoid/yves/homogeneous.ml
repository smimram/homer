(** Test homogenization of presentations. *)

open Stdlib
open FreeMonoid

(* Homogenise *)
let homogenise_rel right star (u, v) =
  let m = Word.length u in 
  let n = Word.length v in 
  if m < n then 
    let fill = Word.make (n - m) star in
    if right = true 
    then (Array.append u fill, v)
    else (Array.append fill u, v)
  else if m > n then
    let fill = Word.make (m - n) star in
    if right = true
    then (u, Array.append v fill)
    else (u, Array.append fill v)
  else (u, v)

let commutation_rel right star x = 
  let x = Word.of_generator x in
  if right = true
  then (Word.append star x, Word.append x star)
  else (Word.append x star, Word.append star x)

let homogenise right rs =
  (* adds a new generator "*" standing for 1 *)
  let rs = add_generator ~name:"*" rs in 
  (* homogenise the existing relations by adding "*" at the end *)
  let star = Array.length rs.generators - 1 in 
  let rs = { rs with rules = IMap.map (homogenise_rel right star) rs.rules } in
  (* adds the commutation relations *|x => x|* *)
  let star = Word.of_generator star in 
  let gens = Array.to_list (Array.init (Array.length rs.generators - 1) (fun i -> i)) in
  let rels = List.map (commutation_rel right star) gens in
  add_rules rs rels

let () =
  LangMonoid.register "rhmg" "Adds a generator '*' (on the right) to make relations homogeneous." 0
    (fun rs a -> homogenise true rs);
  LangMonoid.register "lhmg" "Adds a generator '*' (on the left) to make relations homogeneous." 0
    (fun rs a -> homogenise false rs)

(*************************************************************)
(** Homogeneous completion: adds relations degree by degree **)
(*************************************************************)

(* Homogeneity checks *)
  let is_homogeneous rs (u, v) = 
    Word.degree rs u = Word.degree rs v

let is_homogeneous rs = 
  let rels = IMap.to_list rs.rules in
  List.for_all (is_homogeneous rs) rels

(* Critical pairs of given degree *)
let hcp rs deg =
  let cps = ref [] in
  let empty = ref true in
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
	  let p = Word.degree rs (CRule.source rs cr) in
	  if p = deg then 
            let cs = Array.sub r1 0 l1, s, W.empty in
            cps := (cr,cs) :: !cps
	  else if p > deg then
	    empty := false
      done
    ) rs.rules;
  (!cps, !empty)

(* Inter-reduction of relations of given minimal degree *)
let hcan_right deg rs = 
  let rs = ref rs in
  let eqs = IMap.filter (fun f (u, v) -> Word.degree !rs u >= deg) !rs.rules in
  IMap.iter
    (fun f (u, v) ->
      let v' = normalize !rs v in
      if v' <> v then
        (
         rs := rm_rule !rs f ;
         rs := add_rule !rs (u, v') ;
        )
    ) eqs ;
  !rs

let hcan_dup deg rs =
  let rs = ref rs in
  let eqs = IMap.filter (fun f (u, v) -> Word.degree !rs u >= deg) !rs.rules in
  IMap.iter_pairs ~reflexive:false
    (fun f (u1, u2) g (v1, v2) ->
      if u1 = v1 && u2 = v2 then
        rs := rm_rule !rs g
    ) eqs ;
  !rs

let hcan_left ~lt deg rs =
  let f rs =
    let rs = ref rs in
    let eqs = IMap.filter (fun f (u, v) -> Word.degree !rs u >= deg) !rs.rules in
    try
      IMap.iter_pairs ~symmetric:true ~reflexive:false
        (fun r (r1,r2) s (s1,s2) ->
          for o = 0 to Array.length r1 - Array.length s1 do
            if Array.included o s1 r1 then
              let u = Array.sub r1 0 o in
              (* Printf.printf "incl: %s in %s at %d (%d vs %d)\n" (W.to_string !rs s1) (W.to_string !rs r1) o r s; *)
              let v = Array.sub_right r1 0 (Array.length r1 - Array.length s1 - o) in
              let r1' = normalize !rs (W.concat [u;s2;v]) in
              rs := rm_rule !rs r;
              (* if r1' <> r2 then rs := add_rule ~dup:false !rs (r1',r2) *)
              if r1' <> r2 && lt !rs r1' r2 then rs := add_rule ~dup:false !rs (r2,r1');
              if r1' <> r2 && lt !rs r2 r1' then rs := add_rule ~dup:false !rs (r1',r2);
              (* We restart from the begining as soon as we changed
                 something. *)
              raise Exit
          done) eqs ;
      !rs
    with
    | Exit -> !rs
  in
  fixpoint f rs

let hcan_step ~lt deg rs = 
  let rs = hcan_right deg rs in
  let rs = hcan_dup deg rs in
  hcan_left ~lt deg rs

let hcan ~lt deg rs = 
  fixpoint (hcan_step ~lt deg) rs

(* Completion step *)
let rec hc_step ~lt rs deg = 

  let norm u = normalize rs u in
  let cps, empty = hcp rs deg in

  if cps = [] 

  then 
    if empty = true 
    then rs 
    else hc_step ~lt rs (deg + 1)
    
  else (
    let nb = List.length cps in
    Printf.printf "\nDegree %i:\n" deg ;
    let rec aux i = function
      | [] -> []
      | (f, g) :: cps -> 
	  let x = 100 * i / nb in
	  if x > 100 * (i-1) / nb then 
	    Printf.printf "  critical branchings: %i/%i (%.i%%) \r%!" i nb x ;
	  let u = norm (CRule.target rs f) in 
	  let v = norm (CRule.target rs g) in
	  if u = v 
	  then aux (i+1) cps
	  else
	    let (u, v) = if lt rs u v then (v, u) else (u, v) in
	    (u, v) :: (aux (i+1) cps)
    in 

    let eqs = aux 1 cps in
    let eqs = List.remove_duplicates eqs in

    if eqs = [] 
    
    then ( 
      Printf.printf "\n  all confluent\n%!" ;
      if empty = true 
      then (
	Printf.printf "\nCompletion successful\n\n%!"; 
	rs
       )
      else hc_step ~lt rs (deg + 1)
     )
	  
    else (
      Printf.printf "\n  new relations: %i -> reduction%!" (List.length eqs) ;
      let rs = hcan ~lt deg (add_rules rs ~dup:false eqs) in
      Printf.printf " -> total relations: %i\n%!" (nb_rules rs) ;
      hc_step ~lt rs (deg + 1)
     )
   )

(* Completion *)	
let homogeneous_completion ~lt rs = 
  let rs = canonize ~lt rs in
  if is_homogeneous rs
  then
    let rec aux = function
      | [] -> 0
      | (u, v) :: [] -> Word.degree rs u
      | (u, v) :: rels -> min (Word.degree rs u) (aux rels)
    in 
    let mindeg = aux (IMap.to_list rs.rules) + 1 in
    hc_step ~lt rs mindeg
  else (Printf.printf "Not homogeneous.\n%!" ; rs)

let () =
  LangMonoid.register "kbh" "Optmised Knuth-Bendix completion for homogeneous presentations." 0
    (fun rs a -> homogeneous_completion ~lt:LangMonoid.lt rs)
