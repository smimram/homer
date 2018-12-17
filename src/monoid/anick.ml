(** Anick resolution. *)

open Standard
open FreeMonoid

module G = FreeGroup

module Chain = struct
  (** Anick chains, stored in reversed order. *)
  type t = word list

  let degree c = List.length c

  let word c =
    List.fold_left W.append W.empty (List.rev c)

  let empty : t = []

  let singleton x : t = [W.singleton x]

  let push (c:t) u : t =
    u::c

  let pop (c:t) = List.hd c

  let tl (c:t) = List.tl c

  let to_string rs (c:t) =
    String.concat_map "|" (W.to_string rs) (List.rev c)
end

(** Free right module. *)
module RMod = struct
  (** A generator. *)
  type g = Chain.t * W.t

  (** An element. *)
  type t = g G.t

  let to_string rs (x:t) = G.to_string (fun (c,u) -> Chain.to_string rs c ^ "*" ^ W.to_string rs u) x

  (** Comparison of elements. *)
  let compare rs (c,u) (c',u') =
    let cu = W.append (Chain.word c) u in
    let cu' = W.append (Chain.word c') u' in
    LangMonoid.compare rs cu cu'

  let cgen k x : t = G.cgen k x

  let gen = cgen 1

  let bind : (g -> t) -> (t -> t) = G.bind

  let add : t -> t -> t = G.add

  let sub : t -> t -> t = G.sub

  let zero : t =  G.zero

  let is_zero : t -> bool = G.is_zero
end

(** Anick n-chains. *)
let rec chains rs ?prev n : Chain.t list =
  (* TODO: check that the RS is convergent and reduced *)
  if n = 0 then []
  else if n = 1 then
    let rec aux k = if k < 0 then [] else [W.singleton k]::(aux (k-1)) in
    aux (Array.length rs.generators - 1)
  else
    let chains = match prev with Some chains -> chains | None -> chains rs (n-1) in
    (* TODO: memoize depending on the suffix *)
    let chains =
      List.map
        (fun c ->
          let u = Chain.pop c in
          let ans = ref [] in
          (* Find suffixes *)
          IMap.iter
            (fun r (v,_) ->
              for i = 0 to W.length u - 1 do
                try
                  if W.length v <= W.length u - i then raise Exit;
                  (* Check that v is a suffix of u starting at i *)
                  for j = i to W.length u - 1 do
                    if u.(j) <> v.(j-i) then raise Exit
                  done;
                  let i = W.length u - i in
                  let v' = W.sub v i (W.length v - i) in
                  (* Ensure that the suffix is not reducible by another rule *)
                  let w = W.append u v' in
                  IMap.iter
                    (fun r' (v',_) ->
                      match instance v' w with
                      | Some (_,_,w') ->
                         if r' <> r then raise Exit
                         else if not (W.is_empty w') then raise Exit
                      | None -> ()
                      (* if r' <> r then *)
                        (* if instance v' w <> None then raise Exit *)
                    ) rs.rules;
                  (* Everything is good add the suffix to the list *)
                  ans := (v'::c) :: !ans
                with Exit -> ()
              done;
            ) rs.rules;
          !ans
        ) chains
    in
    List.flatten chains

(** Compute the Anick differential, given a list of chains. *)
let differential rs cc =
  let n = Array.length cc - 2 in
  (* The differential. *)
  let d = Array.init (n+1) (fun i -> G.Map.zero) in
  let df ((c,u):RMod.g) =
    let n = Chain.degree c in
    if n = 0 then RMod.zero else
      let y = G.Map.app d.(n-1) c in
      G.map (fun (c,v) -> c, FreeMonoid.normalize rs (W.append v u)) (G.Map.app d.(n-1) c)
  in
  (* The contacting homotopy. *)
  let rec ch x =
    (* Printf.printf "\nch: %s\n%!" (RMod.to_string rs x); *)
    (* We are only defined on the kernel of the differential. *)
    assert (RMod.is_zero (RMod.bind df x));
    if RMod.is_zero x then RMod.zero else
      (* Leading term of the sum. *)
      let k,(c,u) = G.leading ~compare:(RMod.compare rs) x in
      (* Printf.printf "leading: %s in %s\n%!" (RMod.to_string rs (RMod.cgen k (c,u))) (RMod.to_string rs x); *)
      let n = Chain.degree c in
      if n = 0 then
        let lt =
          (* Printf.printf "deg zero\n"; *)
          if W.is_empty u then
            (* This should not happen with traditional Anick. *)
            (* RMod.cgen k (c,u) *)
            assert false
          else
            let x = u.(0) in
            let u = Array.sub u 1 (Array.length u - 1) in
            RMod.cgen k (Chain.singleton x, u)
        in
        let x' = RMod.sub x (RMod.cgen k (c,u)) in
        (* Extend linearly. *)
        RMod.add lt (ch x')
      else
        let cn = Chain.pop c in
        let c' = Chain.tl c in
        let w = W.append cn u in
        (* Printf.printf "reduction left in %s\n" (W.to_string rs w); *)
        let w1,r,w2 = match reduction_left rs w with Some r -> r | None -> assert false in
        (* Leading term. *)
        let lt =
          let cn' = W.append w1 (Rule.source rs r) in
          let cn' = W.sub cn' (W.length cn) (W.length cn' - W.length cn) in
          let c = Chain.push c cn' in
          RMod.cgen k (c,w2)
        in
        let x' = RMod.sub x (RMod.bind df lt) in
        (* let x' = G.sub x (G.cgen k (c,u)) in *)
        (* let x' = G.add x' (G.cmul k (ch (df (c',normalize rs w)))) in *)
        (* Printf.printf "lt: %s (df: %s)\n%!" (RMod.to_string rs lt) (RMod.to_string rs (RMod.bind df lt)); *)
        (* Printf.printf "x': %s\n%!" (RMod.to_string rs x'); *)
        RMod.add lt (ch x')
  in
  (* Compute d0 *)
  List.iter
    (fun c ->
      d.(0) <- G.Map.set d.(0) c
        (* TODO: this is not actually the usual Anick, where we do not remove the last one. *)
        (* (RMod.sub *)
        (* (RMod.gen (Chain.empty, normalize rs (Chain.pop c))) *)
        (* (RMod.gen (Chain.empty, W.empty)) *)
        (* ); *)
        (RMod.gen (Chain.empty, normalize rs (Chain.pop c)));
      Printf.printf "d ( %s ) = %s\n%!" (Chain.to_string rs c) (RMod.to_string rs (G.Map.app d.(0) c));
    ) cc.(1);
  (* Compute di *)
  for i = 1 to n do
    List.iter
      (fun c ->
        let u = Chain.pop c in
        let c' = Chain.tl c in
        let x = c',u in
        (* Printf.printf "df df %s = %s\n%!" (Chain.to_string rs c) (RMod.to_string rs (df x)); *)
        let x =
          RMod.sub
            (RMod.gen x)
            (ch (df x))
        in
        Printf.printf "d ( %s ) = %s\n%!" (Chain.to_string rs c) (RMod.to_string rs x);
        d.(i) <- G.Map.set d.(i) c x
      ) cc.(i+1)
  done;
  df

module Mat = Matrix.Labeled

(** Rank of the homology groups up to dimension n. *)
let hrank rs n =
  (* The chains. *)
  let cc = Array.make (n+2) [] in
  cc.(0) <- [[]];
  for i = 1 to n+1 do
    cc.(i) <- chains rs ~prev:cc.(i-1) i
  done;
  let df = differential rs cc in
  (* Matrices for the differential. *)
  let d =
    Array.init (n+1)
      (fun i -> Mat.create (Array.of_list cc.(i+1)) (if i = 0 then [||] else Array.of_list cc.(i)))
  in
  for i = 1 to n do
    List.iter (fun c ->
      let x = df (c, W.empty) in
      let x = G.map (fun (c,u) -> c) x in
      G.iter (fun n c' -> Mat.set d.(i) c c' n) x
    ) cc.(i+1)
  done;
  (* Homology ranks. *)
  let h =
    Array.init (n+1)
      (fun i ->
        Printf.printf "H%d: %d / %d\n%!" i (if i = 0 then 1 else Mat.nullity d.(i-1)) (Mat.rank d.(i));
        (if i = 0 then 1 else Mat.nullity d.(i-1)) - Mat.rank d.(i)
      )
  in
  h

let () =
  LangMonoid.register "anick" "Anick chains." 1
    (fun rs a ->
      let n = int_of_string a.(0) in
      let c = chains rs n in
      List.iter (fun c -> Lang.printf "%s\n" (Chain.to_string rs c)) c;
      rs
    );
  LangMonoid.register "H" "Rank of homology group." 1
    (fun rs a ->
      let h = hrank rs (int_of_string a.(0)) in
      let h = Array.to_list h in
      let h = List.map string_of_int h in
      let h = String.concat " " h in
      Lang.printf "%s\n" h;
      rs
    )
