(** Generate presentations of usual monoids. *)

open FreeMonoid

let artin_type_of_string t =
  try
    let t = String.uppercase_ascii t in
    let n = int_of_string (String.sub t 1 (String.length t - 1)) in
    match t.[0] with
    | 'A' -> `A n
    | 'B' -> `B n
    | 'D' -> `D n
    | 'E' -> `E n
    | 'H' -> `H n
    | 'I' -> `I2 n
    | _ -> raise Exit
  with
  | _ -> failwith (Printf.sprintf "Unknown Artin type: %S." t)

let artin ?(coxeter=false) t =
  let t = artin_type_of_string t in
  let rs = ref (create ()) in
  let gen n =
    for i = 0 to n - 1 do
      rs := add_generator !rs;
      if coxeter then rs := add_rule !rs ([|i;i|],[||])
    done;
  in
  (
    match t with
    | `A n ->
	gen n;
	for i = 0 to n - 2 do
	  rs := add_rule !rs ([|i+1;i;i+1|],[|i;i+1;i|])
	done;
	for i = 0 to n - 1 do
	  for j = i + 2 to n - 1 do
	    rs := add_rule !rs ([|j;i|],[|i;j|])
	  done;
	done
    | `B n ->
	gen n;
	rs := add_rule !rs ([|1;0;1;0|],[|0;1;0;1|]);
	for i = 1 to n - 2 do
	  rs := add_rule !rs ([|i+1;i;i+1|],[|i;i+1;i|])
	done;
	for i = 0 to n - 1 do
	  for j = i + 2 to n - 1 do
	    rs := add_rule !rs ([|j;i|],[|i;j|])
	  done;
	done
    | `D n ->
	gen n;
	rs := add_rule !rs ([|2;0;2|],[|0;2;0|]);
	for i = 1 to n - 2 do
	  rs := add_rule !rs ([|i+1;i;i+1|],[|i;i+1;i|])
	done;
	rs := add_rule !rs ([|1;0|],[|0;1|]);
	for j = 3 to n - 1 do
	  rs := add_rule !rs ([|j;0|],[|0;j|])
	done;
	for i = 1 to n - 1 do
	  for j = i + 2 to n - 1 do
	    rs := add_rule !rs ([|j;i|],[|i;j|])
	  done;
	done
    | `E n ->
	gen n;
	rs := add_rule !rs ([|3;0;3|],[|0;3;0|]);
	for i = 1 to n - 2 do
	  rs := add_rule !rs ([|i+1;i;i+1|],[|i;i+1;i|])
	done;
	rs := add_rule !rs ([|1;0|],[|0;1|]);
	rs := add_rule !rs ([|2;0|],[|0;2|]);
	for j = 4 to n - 1 do
	  rs := add_rule !rs ([|j;0|],[|0;j|])
	done;
	for i = 1 to n - 1 do
	  for j = i + 2 to n - 1 do
	    rs := add_rule !rs ([|j;i|],[|i;j|])
	  done;
	done
    | `H n ->
	gen n;
	rs := add_rule !rs ([|1;0;1;0;1|],[|0;1;0;1;0|]);
	for i = 1 to n - 2 do
	  rs := add_rule !rs ([|i+1;i;i+1|],[|i;i+1;i|])
	done;
	for i = 0 to n - 1 do
	  for j = i + 2 to n - 1 do
	    rs := add_rule !rs ([|j;i|],[|i;j|])
	  done;
	done
    | `I2 p ->
	gen 2;
	let u = Array.init p (fun i -> if i mod 2 = 0 then 1 else 0) in
	let v = Array.init p (fun i -> if i mod 2 = 0 then 0 else 1) in
	rs := add_rule !rs (u,v)
  );
  !rs

let coxeter = artin ~coxeter:true

let () =
  LangMonoid.register "artin" "Generate an Artin-Tits presentation." 1
    (fun rs a -> artin a.(0));
  LangMonoid.register "coxeter" "Generate a Coxeter presentation." 1
    (fun rs a -> coxeter a.(0))

let plactic ?(numbers=false) n =
  let rs = ref (create ()) in
  for i = 0 to n - 1 do
    if numbers then
      rs := add_generator ~name:(string_of_int (i+1)) !rs
    else
      rs := add_generator !rs;
  done;
  for x = 0 to n - 1 do
    for y = x to n - 1 do
      for z = y + 1 to n - 1 do
        rs := add_rule !rs ([|z;x;y|],[|x;z;y|])
      done
    done
  done;
  for x = 0 to n - 1 do
    for y = x+1 to n - 1 do
      for z = y to n - 1 do
        rs := add_rule !rs ([|y;z;x|],[|y;x;z|])
      done
    done
  done;
  !rs

let () =
  LangMonoid.register "plactic" "Generate a plactic monoid." 1
    (fun rs a -> plactic (int_of_string a.(0)));
  LangMonoid.register "placticn" "Generate a plactic monoid, with numbers as generators." 1
    (fun rs a -> plactic ~numbers:true (int_of_string a.(0)))

let chinese n =
  let rs = ref (create ()) in
  for i = 0 to n - 1 do
    rs := add_generator !rs ;
  done ;
  for a = 0 to n - 2 do
    for b = a + 1 to n - 1 do
      rs := add_rule !rs ([|b;b;a|], [|b;a;b|]) ;
      rs := add_rule !rs ([|b;a;a|], [|a;b;a|])
    done
  done ;
  for a = 0 to n - 3 do
    for b = a + 1 to n - 2 do
      for c = b + 1 to n - 1 do
        rs := add_rule !rs ([|c;b;a|], [|b;c;a|]) ;
        rs := add_rule !rs ([|c;a;b|], [|b;c;a|])
      done
    done
  done ;
  !rs

let () =
  LangMonoid.register "chinese" "Generate a chines monoid." 1
    (fun rs a -> chinese (int_of_string a.(0)))

let absorb n =
  let rs = ref (create ()) in
  rs := add_generators !rs n;
  for i = 0 to n - 1 do
    for j = 0 to n - 1 do
      rs := add_rule !rs ([|i;j|],[|i|])
    done
  done;
  !rs

let () =
  LangMonoid.register "absorb" "Monoid in which every letter is left absorbant." 1
    (fun rs a -> absorb (int_of_string a.(0)))

let perm n =
  let rs = ref (create ()) in
  rs := add_generators !rs n;
  for i = 0 to n - 1 do
    for j = i + 1 to n - 1 do
      rs := add_rule !rs ([|j;i|],[|i;j|])
    done
  done;
  !rs

let () =
  LangMonoid.register "perm" "Monoid with n pairwise commuting generators." 1
    (fun rs a -> perm (int_of_string a.(0)))
