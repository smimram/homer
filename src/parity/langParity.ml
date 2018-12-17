(** Part of the language specific to parity complexes. *)

open Standard
open Parity

(** Current signature. *)
let s = ref Sig.empty
(** Current cell. *)
let c = ref Cell.empty

let printf = Lang.printf

let print_sig ?(categorical=false) () =
  if not categorical then
    printf "%s\n%!" (Sig.to_string !s)
  else
    printf "%s%!" (Cat.string_of_sig !s)

let print_cell () =
  printf "%s\n%!" (Cell.to_string !c);
  let str c = Cat.to_string (Cat.simpl !s (Cat.of_cell !s c)) in
  if Cell.dim !c = 0 then
    printf "%s\n%!" (str !c)
  else
    (* printf "%s\n%!" (Cat.to_string c); *)
    printf "%s : %s -> %s\n%!"
      (str !c)
      (str (Cell.source !s !c))
      (str (Cell.target !s !c))

(** Register a new command *)
let register ?(undo=true) name doc args f =
  let mode = "parity" in
  let f a =
    try
      let old = !s, !c in
      let s', c' = f !s !c a in
      s := s';
      c := c';
      if !s <> fst old then (if !Lang.verbose then print_sig ())
      else if !c <> snd old then (if !Lang.verbose then print_cell ());
      fun () ->
        s := fst old; c := snd old
    with
    | Parity.Signature.Invalid s -> failwith ("Invalid signature (" ^ s ^ ").")
    | Parity.Cell.Invalid s -> failwith ("Invalid cell (" ^ s ^ ").")
  in
  if undo then
    Lang.register_with_undo ~mode name doc args f
  else
    let f a = let _ = f a in () in
    Lang.register ~mode name doc args f

(** Register a command with aliases. *)
let registers ?undo names doc args f =
  List.iter (fun name -> register ?undo name doc args f) names

module Set = struct
  include Set

  let parse s =
    Set.make (String.split_char s ',')
end

let () =
  register ~undo:false "sig" "Display current signature." 0 (fun s c _ -> print_sig (); s,c);
  register ~undo:false "sigl" "Display current signature (one generator per line)." 0 (fun s c _ ->
    for n = 0 to Sig.max_dim s do
      Set.iter (fun g ->
        printf "%d : %s : %s -> %s\n" n g
          (Set.to_string (Sig.source s g))
          (Set.to_string (Sig.target s g))
      ) (Sig.generators ~n s)
    done;
    s,c);
  register ~undo:false "sign" "Display generators of given dimension." 1 (fun s c a ->
    let n = int_of_string a.(0) in
    let gg = Sig.generators ~n s in
    let count =
      let k = Set.card gg in
      if k >= 10 then "\n("^string_of_int k^" elements)" else ""
    in
    printf "%s%s\n" (Set.to_string ~sep:" , " gg) count;
    s,c
  );
  register ~undo:false "sigcat" "Display current signature with categorical source and targets." 0 (fun s c _ -> print_sig ~categorical:true (); s,c);
  register ~undo:false "dim" "Dimension of a generator." 1 (fun s c a ->
    printf "%d\n" (Sig.dim s a.(0));
    s,c
  );
  register ~undo:false "cell" "Display current cell." 0 (fun s c _ -> print_cell (); s,c);
  register "gen" "Add a generator." (-1) (fun s c a ->
    let name = a.(0) in
    let s =
      if Array.length a = 1 then
        Sig.add s name 0 (Set.empty, Set.empty)
      else
        let src, tgt =
          if Array.length a = 3 then a.(1), a.(2)
          else if Array.length a = 5 then a.(2), a.(4)
          else failwith "Wrong number of arguments."
        in
        let src = Set.parse src in
        let tgt = Set.parse tgt in
        let n = Sig.dim s (Set.element src) + 1 in
        Sig.add s name n (src, tgt)
    in
    let c = Cell.full s in
    s, c
  );
  register ~undo:false "cellng" "Number of generators in current cell." 0 (fun s c _ ->
    let k = ref 0 in
    for i = 0 to Cell.dim c do
      let n = Set.card c.(i) in
      printf "%d : %d\n" i n;
      k := !k + n
    done;
    printf "* : %d\n" !k;
    s, c);
  register ~undo:false "cosources" "Cosources of a given generator in current cell." 1 (fun s c a ->
    let g = a.(0) in
    let n = Sig.dim s g in
    let gg = c.(n+1) in
    let gg = Set.filter (fun g' -> Set.mem (Sig.source s g') g) gg in
    printf "%s\n" (Set.to_string ~sep:" , " gg);
    s, c
  );
  register ~undo:false "cotargets" "Cotargets of a given generator in current cell." 1 (fun s c a ->
    let g = a.(0) in
    let n = Sig.dim s g in
    let gg = c.(n+1) in
    let gg = Set.filter (fun g' -> Set.mem (Sig.target s g') g) gg in
    printf "%s\n" (Set.to_string ~sep:" , " gg);
    s, c
  );
  register ~undo:false "cofaces" "Cofaces of a given generator in current cell." 1 (fun s c a ->
    let g = a.(0) in
    let n = Sig.dim s g in
    let gg = c.(n+1) in
    let gg = Set.filter (fun g' -> Set.mem (Sig.source s g') g || Set.mem (Sig.target s g') g) gg in
    printf "%s\n" (Set.to_string ~sep:" , " gg);
    s, c
  );
  register ~undo:false "type" "Type of a generator." 1 (fun s c a ->
    let g = a.(0) in
    let src = Set.to_string ~sep:"," (Sig.source s g) in
    let tgt = Set.to_string ~sep:"," (Sig.target s g) in
    printf "%s : %s -> %s\n" g src tgt;
    s,c
  );
  register ~undo:false "ctype" "Categorical type of a generator." 1 (fun s c a ->
    let g = a.(0) in
    let n = Sig.dim s g in
    let sc c =
      let c = Cell.generators s (n-1) c in
      let c = Cat.of_cell s c in
      let c = Cat.simpl s c in
      Cat.to_string c
    in
    let src = sc (Sig.source s g) in
    let tgt = sc (Sig.target s g) in
    printf "%s : %s -> %s\n" g src tgt;
    s,c
  );
  register "full" "Use full cell." 0 (fun s c _ -> s, Cell.full s);
  register "generator" "Cell associated to a generator (or a list of generators)." (-1) (fun s c a ->
    let l = Array.to_list a in
    assert (l <> []);
    s, Cell.generators_list s l);
  register "source" "Source of the cell." 0 (fun s c _ -> s, Cell.source s c);
  register "target" "Target of the cell." 0 (fun s c _ -> s, Cell.target s c);
  register ~undo:false "check" "Sanity checks on signature and cell." 0 (fun s c _ -> Cell.check_signature s; Cell.check s c; s, c);
  register ~undo:false "checko" "Check that orientations of generators are compatible." 0 (fun s c _ -> Sig.check_orientation s; s,c);
  register "reorient" "Change the orientation of a cell." 1 (fun s c a ->
    let s = Sig.reorient s a.(0) in
    s, c);
  register "coreorient" "Change the orientation of a cell." 1 (fun s c a ->
    let s = Sig.coreorient s a.(0) in
    s, c);
  registers ["bireorient";"bro"] "Change the orientation of a cell." 1 (fun s c a ->
    let s = Sig.reorient s a.(0) in
    let s = Sig.coreorient s a.(0) in
    s, c);
  register "remove" "Remove a generator." 1 (fun s c a ->
    let s = Sig.remove s a.(0) in
    s, Cell.full s);
  register "cube" "Generate a cube." 1 (fun s c a ->
    let n = int_of_string a.(0) in
    let s = GenerateParity.cube n in
    s, Cell.full s
  );
  register "simplex" "Generate a simplex." 1 (fun s c a ->
    let n = int_of_string a.(0) in
    let s = GenerateParity.simplex n in
    s, Cell.full s
  );
  register "globe" "Generate a globe (or a tensor of globes)." (-1) (fun s c a ->
    let s =
      if Array.length a = 1 then
        let n = int_of_string a.(0) in
        GenerateParity.globe n
      else if Array.length a = 2 then
        let n1 = int_of_string a.(0) in
        let n2 = int_of_string a.(1) in
        let globe x n = GenerateParity.globe ~src:(fun i -> x^string_of_int i^"⁻") ~tgt:(fun i -> x^string_of_int i^"⁺") ~top:x n in
        let s1 = globe "x" n1 in
        let s2 = globe "y" n2 in
        Sig.tensor s1 s2
      else
        failwith "Wrong number of arguments."
    in
    s, Cell.full s
  );
  register "empty" "The empty signature." 0 (fun s c a ->
    let s = Sig.empty in
    s, Cell.full s);
  register ~undo:false "graphviz" "Graph of the maximal cells in graphviz format." 0 (fun s c _ ->
    let n = Cell.dim c in
    let gg = Cell.elements c n in
    let dot = Sig.dot s gg in
    printf "%s" dot;
    let oc = open_out "graph.dot" in
    output_string oc dot;
    close_out oc;
    s,c
  );
(*
  register "cotrunc" "Cotruncation of the signature: (n+1)-cells become n-cells." 0 (fun s c _ ->
    let s = Sig.cotrunc s in
    s, Cell.full s
  )
*)
