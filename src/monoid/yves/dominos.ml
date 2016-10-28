(** Test dominos. *) 

open Stdlib
open FreeMonoid

module IIMap = struct
  include Map.Make (struct type t = int * int let compare = Pervasives.compare end)
  let eval theta (u, v) =
    try find (u, v) theta
    with Not_found -> (u, v)
  let eval1 theta (u, v, w) = 
    let (u', v') = eval theta (u, v) in 
    (u', v', w)
  let eval2 theta (u, v, w) = 
    let (v', w') = eval theta (v, w) in 
    (u, v', w')
end

let theta rs = 
  let rec aux accu = function
    | [] -> accu
    | (u, v) :: rules -> 
	let accu = IIMap.add (u.(0), u.(1)) (v.(0), v.(1)) accu in 
	aux accu rules
  in 
  let rules = List.map snd (IMap.bindings rs.rules) in
  aux IIMap.empty rules

let normclass_triple verb rs theta (u, v, w) =
  let rec left n (u, v, w) = 
    let (u', v') = theta (u, v) in
    if (u', v') = (u, v) then n
    else right (n+1) (u', v', w)
  and right n (u, v, w) = 
    let (v', w') = theta (v, w) in
    if (v', w') = (v, w) then n
    else left (n+1) (u, v', w')
  in 
  let m = left 0 (u, v, w) in 
  let n = right 0 (u, v, w) in
  let (m, n) = match (m, n) with 
  | (0, 0) -> (0, 0)
  | (0, n) -> (-1, n)
  | (m, 0) -> (m, -1)
  | (m, n) -> (m, n) 
  in
  if verb = true || m > 3 || n > 3 then
    Printf.printf "%s|%s|%s : %i %i\n" (rs.generators.(u)) (rs.generators.(v)) (rs.generators.(w)) m n ;
  (m, n)
    
let normclass verb rs = 
  let maxleft = ref 0 in
  let maxright = ref 0 in
  let n = Array.length rs.generators in
  let theta = IIMap.eval (theta rs) in
  for u = 0 to n - 1 do
    for v = 0 to n - 1 do 
      for w = 0 to n - 1 do
	let (m, n) = normclass_triple verb rs theta (u, v, w) in
	if m > !maxleft then maxleft := m ;
	if n > !maxright then maxright := n
      done 
    done
  done ;
  (!maxleft, !maxright)

let modclass_triple verb unit rs theta (u, v, w) =
  let rec left n (u, v, w) = 
    let (u', v') = theta (u, v) in
    if (u', v') = (u, v) then n
    else 
      let n' =
	if (u = unit && v' = unit && u' = v) || (v = unit && u' = unit && v' = u)
	then n
	else n+1
      in right n' (u', v', w)
  and right n (u, v, w) = 
    let (v', w') = theta (v, w) in
    if (v', w') = (v, w) then n
    else 
      let n' =
	if (v = unit && w' = unit && v' = w) || (w = unit && v' = unit && w' = v)
	then n
	else n+1
      in left n' (u, v', w')
  in 
  let m = left 0 (u, v, w) in 
  let n = right 0 (u, v, w) in
  let (m, n) = match (m, n) with 
  | (0, 0) -> (0, 0)
  | (0, n) -> (-1, n)
  | (m, 0) -> (m, -1)
  | (m, n) -> (m, n) 
  in
  if verb = true || m > 3 || n > 3 then
    Printf.printf "%s|%s|%s : %i %i\n" (rs.generators.(u)) (rs.generators.(v)) (rs.generators.(w)) m n ;
  (m, n)
    
let modclass verb unit rs = 
  let maxleft = ref 0 in
  let maxright = ref 0 in
  let n = Array.length rs.generators in
  let theta = IIMap.eval (theta rs) in
  let unit = Array.index rs.generators unit in
  for u = 0 to n - 1 do
    for v = 0 to n - 1 do 
      for w = 0 to n - 1 do
	let (m, n) = modclass_triple verb unit rs theta (u, v, w) in
	if m > !maxleft then maxleft := m ;
	if n > !maxright then maxright := n
      done 
    done
  done ;
  (!maxleft, !maxright)

let domino1 rs = 
  let ans = ref true in
  let n = Array.length rs.generators in
  let theta = IIMap.eval (theta rs) in
  for u = 0 to n - 2 do
    for v = 0 to n - 2 do
      let (u', v') = theta (u, v) in 
      if (u', v') <> (u, v) then
	for w = 0 to n - 2 do 
	  if theta (v, w) = (v, w) then
	    let (v'', w') = theta (v', w) in 
	    let (u'', v''') = theta (u', v'') in
	    if (u'', v''') <> (u', v'') then (
	      Printf.printf "%s|%s|%s => %s|%s|%s => %s|%s|%s !!! %s|%s => %s|%s\n%!" 
		(rs.generators.(u)) (rs.generators.(v)) (rs.generators.(w))
		(rs.generators.(u')) (rs.generators.(v')) (rs.generators.(w))
		(rs.generators.(u')) (rs.generators.(v'')) (rs.generators.(w'))
		(rs.generators.(u')) (rs.generators.(v''))
		(rs.generators.(u'')) (rs.generators.(v''')) ;
	      ans := false
	     )
	done
    done
  done ;
  !ans

let domino2 rs = 
  let ans = ref true in
  let n = Array.length rs.generators in
  let theta = IIMap.eval (theta rs) in
  for u = 0 to n - 2 do
    for v = 0 to n - 2 do
      if (u, v) = theta (u, v) then 
	for w = 0 to n - 2 do
	  let (v', w') = theta (v, w) in
	  if (v', w') <> (v, w) then 
	    let (u', v'') = theta (u, v') in 
	    let (v''', w'') = theta (v'', w') in 
	    if (v''', w'') <> (v'', w') then (
	      Printf.printf "%s|%s|%s => %s|%s|%s => %s|%s|%s !!! %s|%s => %s|%s\n%!" 
		(rs.generators.(u)) (rs.generators.(v)) (rs.generators.(w))
		(rs.generators.(u)) (rs.generators.(v')) (rs.generators.(w'))
		(rs.generators.(u')) (rs.generators.(v'')) (rs.generators.(w'))
		(rs.generators.(v'')) (rs.generators.(w'))
		(rs.generators.(v''')) (rs.generators.(w'')) ;
	       ans := false
	     )
	done
    done
  done ;
  !ans

let () =
  LangMonoid.register "domino1" "Checks if domino 1 holds." 0
    (fun rs a -> 
      Lang.printf "Domino 1: %b\n" (domino1 rs) ;
      rs
    );
  LangMonoid.register "domino2" "Checks if domino 2 holds." 0
    (fun rs a -> 
      Printf.printf "Domino 2: %b\n" (domino2 rs) ;
      rs
    )
