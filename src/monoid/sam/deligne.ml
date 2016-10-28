(** Completion test. *)

open Stdlib
open FreeMonoid

let deligne rs =
  (* All the rules *)
  let rules =
    let ans = ref [] in
    IMap.iter
      (fun _ r ->
        ans := r :: !ans
      ) rs.rules;
    !ans
  in
  let left = List.rev_map fst rules in
  let right = List.rev_map snd rules in
  (* Compute length 2 words. *)
  let subwords a =
    let ans = ref [] in
    for i = 0 to Array.length a - 2 do
      ans := Array.sub a i 2 :: !ans
    done;
    !ans
  in
  let w = List.rev_map subwords (left@right) in
  let w = List.concat w in
  let w = List.remove_duplicates w in
  let rs = ref rs in
  (* Add new generators. *)
  List.iter
    (fun w ->
      let l w =
        let l = !rs.generators.(w) in
        if l.[0] = '$' then String.sub l 1 (String.length l - 1)
        else l
      in
      let g = "$" ^ l w.(0) ^ l w.(1) in
      if not (has_generator !rs g) then
        (
          rs := add_generator !rs ~name:g;
          let g = nb_generators !rs - 1 in
          rs := add_rule ~dup:false !rs (w,[|g|])
        )
    ) w;
  (* Complete structural rules. *)
  (*
    let loop = ref true in
    while !loop do
    loop := false;
    rs := canonize_right !rs;
    rs := canonize_left !rs;
    Printf.printf "\nDL: %s\n%!" (to_string !rs);
    let cr = critical_rules !rs in
    List.iter
    (fun (u,v) ->
    (* TODO: other cases? *)
    if Array.length u = 2 && Array.length v = 2 then
    let d g = !rs.generators.(g).[0] = '$' in
    let l g =
    let l = !rs.generators.(g) in
    if l.[0] = '$' then String.sub l 1 (String.length l - 1)
    else l
    in
    (* TODO: this might be wrong if we have letters with multiple letters
    as labels... *)
    if l u.(0) ^ l u.(1) = l v.(0) ^ l v.(1) then
    (
    assert ((d u.(0) || d u.(1)) && (d v.(0) || d v.(1)));
    (* Printf.printf "No $ in %s <-> %s\n%!" (W.to_string !rs u) (W.to_string !rs v); *)
    let lg = Printf.sprintf "$%s%s" (l u.(0)) (l u.(1)) in
    let g =
    try
    Array.index !rs.generators lg
    with
    | Not_found ->
    rs := add_generator !rs ~name:lg;
    nb_generators !rs - 1
    in
    rs := add_rule !rs (u,[|g|]);
    loop := true
    )
    ) cr
    done;
  *)
  !rs

let () =
  LangMonoid.register "deligne" "" 0
    (fun rs a -> deligne rs);
  LangMonoid.register "dc" "" 0
    (fun rs a -> fixpoint (fun rs -> canonize ~lt:LangMonoid.lt (deligne rs)) rs)
