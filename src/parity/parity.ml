(** Parity complexes. *)

open Standard

module Poset = Poset.Labeled

(** Way to display composition. *)
let composition = ref (`Sequential : [`Sequential | `Categorical])
(** Show identities. *)
let show_identities = ref false
let use_utf8 = ref true

type generator = string

(** Sets of generators. *)
module Set = struct
  type 'a set = 'a SimpleSet.t
  include (SimpleSet : module type of SimpleSet with type 'a t := 'a set)
  type t = generator set
  let to_string ?(sep=",") gg = to_string sep id gg
end

(** Operations on signatures. *)
module Signature = struct
  (* Generator, dimension, source, target. *)
  type t = (generator * (int * Set.t * Set.t)) list

  let empty : t = []

  let mem (s : t) g = List.mem_assoc g s

  (** Dimension of a generator. *)
  let dim s g =
    assert (mem s g);
    let n,_,_ = List.assoc g s in
    n

  (** Boundary of a generator in the signature. *)
  let d (s : t) g =
    assert (mem s g);
    let n,s,t = List.assoc g s in
    s,t

  let source s g = fst (d s g)

  let target s g = snd (d s g)

  (** Raised when the signature is not valid. *)
  exception Invalid of string

  (** Ensure that a set of generators is well formed. *)
  let well_formed s gg =
    if Set.is_empty gg then () else
      let n = dim s (Set.element gg) in
      assert (Set.for_all (fun g -> dim s g = n) gg);
      if n = 0 then if not (Set.is_singleton gg) then raise (Invalid "non-singleton point");
      List.iter_ordered_pairs (fun g1 g2 ->
        if not (Set.is_empty (Set.inter (source s g1) (source s g2))) then raise (Invalid ("intersecting sources: "^g1^" and "^g2));
        if not (Set.is_empty (Set.inter (target s g1) (target s g2))) then raise (Invalid ("intersecting targets: "^g1^" and "^g2))
      ) (Set.to_list gg)
  let well_formed s gg =
    try well_formed s gg; true with Invalid _ -> false

  (** Add a generator to a signature. *)
  (* TODO: we could remove n since it can be infered from source and target *)
  let add (s : t) g n (src,tgt) : t =
    (* Printf.printf "add %s : %s -> %s\n%!" g (Set.to_string src) (Set.to_string tgt); *)
    assert (n >= 0);
    if mem s g then failwith "Generator already present.";
    assert (iff (Set.is_empty src) (n = 0));
    assert (iff (Set.is_empty tgt) (n = 0));
    assert (not (n = 1) || Set.is_singleton src);
    assert (not (n = 1) || Set.is_singleton tgt);
    assert (Set.for_all (fun g -> mem s g) src);
    assert (Set.for_all (fun g -> dim s g = n - 1) src);
    assert (Set.for_all (fun g -> mem s g) tgt);
    assert (Set.for_all (fun g -> dim s g = n - 1) tgt);
    assert (Set.is_empty (Set.inter src tgt));
    (* Street's axiom 1. *)
    let () =
      let ss = Set.bind (source s) src in
      let tt = Set.bind (target s) tgt in
      let st = Set.bind (source s) tgt in
      let ts = Set.bind (target s) src in
      if not (Set.eq (Set.union ss tt) (Set.union st ts)) then raise (Invalid "not pre-globular")
    in
    if not (well_formed s src) then raise (Invalid "source not well-formed");
    if not (well_formed s tgt) then raise (Invalid "target not well-formed");
    s@[g,(n,src,tgt)]

  let generators ?n (s : t) =
    let gg = List.map fst s in
    let gg = Set.make gg in
    match n with
    | None -> gg
    | Some n -> Set.filter (fun g -> dim s g = n) gg

  let max_dim s =
    Set.fold (fun n g -> max n (dim s g)) (-1) (generators s)

  (** String representation of a signature. *)
  let to_string (s : t) =
    (*
    String.concat_map "\n"
      (fun (g,(n,s,t)) ->
        g ^
          if n = 0 then "" else
            (" : " ^ Set.to_string s ^ " -> " ^ Set.to_string t)
      ) (List.rev s)
    *)
    let ans = ref "" in
    ans := Set.to_string ~sep:" , " (generators ~n:0 s);
    for n = 1 to max_dim s do
      ans := !ans ^ "\n";
      ans := !ans ^ SimpleSet.to_string " , "
        (fun g ->
          Printf.sprintf "%s : %s -> %s" g
            (Set.to_string (source s g))
            (Set.to_string (target s g))
        ) (generators ~n s);
    done;
    !ans

  (** Check that generator have non-conflicting orientations. *)
  let check_orientation s =
    (*
    let f gg =
      Set.iter_ordered_pairs (fun g1 g2 ->
        (* Printf.printf "check %s vs %s\n" g1 g2; *)
        if not (Set.is_empty (Set.inter (source s g1) (source s g2))) then raise (Invalid ("intersecting sources: "^g1^" and "^g2));
        if not (Set.is_empty (Set.inter (target s g1) (target s g2))) then raise (Invalid ("intersecting targets: "^g1^" and "^g2))
      ) gg
    in
    for n = 0 to max_dim s do
      Set.iter (fun g ->
        (* Printf.printf "%s\n%!" g; *)
        (* f (Set.union (source s g) (target s g)) *)
        f (source s g);
        f (target s g)
      ) (generators ~n s)
    done
    *)
    let f ssrc ttgt gg =
      Set.iter_ordered_pairs (fun g1 g2 ->
        (* Printf.printf "check %s vs %s\n" g1 g2; *)
        if not (Set.is_empty (Set.diff (Set.inter (source s g1) (source s g2)) ssrc)) then raise (Invalid ("intersecting sources: "^g1^" and "^g2));
        if not (Set.is_empty (Set.diff (Set.inter (target s g1) (target s g2)) ttgt)) then raise (Invalid ("intersecting targets: "^g1^" and "^g2))
      ) gg
    in
    for n = 0 to max_dim s do
      Set.iter (fun g ->
        (* Printf.printf "%s\n%!" g; *)
        (* f (Set.union (source s g) (target s g)) *)
        let src = source s g in
        let tgt = target s g in
        let bnd = Set.union src tgt in
        let ssrc = Set.diff (Set.bind (source s) bnd) (Set.bind (target s) bnd) in
        let ttgt = Set.diff (Set.bind (target s) tgt) (Set.bind (source s) bnd) in
        Printf.printf "ssrc: %s\n%!" (Set.to_string ssrc);
        Printf.printf "ttgt: %s\n%!" (Set.to_string ttgt);
        f ssrc ttgt bnd
      ) (generators ~n s)
    done

  (** Test whether two generators are immediate successors. *)
  let succ s g h =
    assert (dim s g = dim s h);
    not (Set.is_empty (Set.inter (target s g) (source s h)))

  (** Partial order on a set of n generators wrt to dimension n-1. *)
  let le s gg =
    assert (not (Set.is_empty gg));
    let n = dim s (Set.element gg) in
    assert (Set.for_all (fun g -> dim s g = n) gg);
    let le = Poset.create (Set.to_list gg) in
    Set.iter (fun g ->
      Set.iter (fun h ->
        if succ s g h then Poset.add le g h
      ) gg) gg;
    le

  (** Tensor product of two signatures. *)
  let tensor ?(sep="|") s s' =
    let gen_tens g h = g ^ sep ^ h in
    let n = max_dim s in
    let n' = max_dim s' in
    let ans = ref empty in
    for i = 0 to n + n' do
      for j = 0 to i do
        Set.iter (fun g ->
          Set.iter (fun h ->
            let gh = gen_tens g h in
            let src =
              Set.union
                (Set.map (fun g -> gen_tens g h) (source s g))
                (Set.map (fun h -> gen_tens g h) ((if dim s g mod 2 = 0 then source else target) s' h))
            in
            let tgt =
              Set.union
                (Set.map (fun g -> gen_tens g h) (target s g))
                (Set.map (fun h -> gen_tens g h) ((if dim s g mod 2 = 0 then target else source) s' h))
            in
            ans := add !ans gh i (src,tgt)
          ) (generators ~n:(i-j) s')
        ) (generators ~n:j s)
      done
    done;
    !ans

  (** Change the orientation of a generator. *)
  let reorient s g : t =
    if not (mem s g) then failwith ("Cell not found: "^g);
    List.map (fun (g',(n,s,t)) ->
      if g' = g then g',(n,t,s)
      else g',(n,s,t)
    ) s

  let coreorient s g : t =
    assert (mem s g);
    let n = dim s g in
    List.map (fun (g',(n',s,t)) ->
      if n' <> n+1 then
        g',(n',s,t)
      else
        let s, t =
          if Set.mem s g then
            Set.remove s g, Set.add t g
          else if Set.mem t g then
            Set.add s g, Set.remove t g
          else
            s, t
        in
        g',(n',s,t)
    ) s

  let bireorient s g =
    coreorient (reorient s g) g

  (** Remove a generator. *)
  let remove (s:t) g : t =
    List.may_map
      (fun (g',(n,s,t)) ->
        if g' = g then None
        else
          let ans = g',(n,s,t) in
          assert (not (Set.mem s g));
          assert (not (Set.mem t g));
          Some ans
      ) s

  (* (\** Truncate signature at given dimension. *\) *)
  (* let trunc s n = *)
    (* let  *)

  (** Underlining graph. *)
  let graph s =
    let vertices = generators ~n:0 s in
    let vertices = Set.to_list vertices in
    let edges = generators ~n:1 s in
    let edges = Set.to_list edges in
    let edges = List.map (fun g -> Set.element (source s g), g, Set.element (target s g)) edges in
    Graph.make vertices edges

  (** Zero-source of a generator. *)
  let zsource s g =
    let aux gg = Set.diff (Set.bind (source s) gg) (Set.bind (target s) gg) in
    Set.the_element (iter (dim s g) aux (Set.singleton g))

  (** Zero-target of a generator. *)
  let ztarget s g =
    let aux gg = Set.diff (Set.bind (target s) gg) (Set.bind (source s) gg) in
    Set.the_element (iter (dim s g) aux (Set.singleton g))

(*
  (** Remove 0-cells from a signature. *)
  let cotrunc s =
    let graph = graph s in
    let paths = Graph.paths graph in
    (* Initial/terminal vertex and paths from/to it. *)
    let init = match Graph.Vertex.initial graph with [x] -> x | _ -> assert false in
    let term = match Graph.Vertex.terminal graph with [x] -> x | _ -> assert false in
    Printf.printf "init: %s\n%!" init;
    Printf.printf "term: %s\n%!" term;
    let init_paths =
      List.may_map (fun p ->
        if Graph.Path.source graph p = init then
          Some (Graph.Path.target graph p, p)
        else
          None
      ) paths
    in
    let term_paths =
      List.may_map (fun p ->
        if Graph.Path.target graph p = term then
          Some (Graph.Path.source graph p, p)
        else
          None
      ) paths
    in
    (* A generator in a context. *)
    let ctxt p g q =
      let p =
        if Graph.Path.is_empty p then ""
        else Graph.Path.to_string p ^ "."
      in
      let q =
        if Graph.Path.is_empty q then ""
        else "." ^ Graph.Path.to_string q
      in
      p ^ g ^ q
    in
    (* Construct the new signature. *)
    let s' = ref empty in
    for n = 1 to max_dim s do
      Set.iter (fun g ->
        try
          let x = zsource s g in
          let y = ztarget s g in
          Printf.printf "adding: %s : %s -> %s\n%!" g x y;
          (* We don't want to add the same path multiple times. *)
          if n = 1 && x <> init then raise Exit;
          List.iter (fun p ->
            List.iter (fun q ->
              let ctxt g = ctxt p g q in
              let src, tgt =
                if n = 1 then Set.empty, Set.empty else
                  let src = source s g in
                  let tgt = target s g in
                  let src = Set.map ctxt src in
                  let tgt = Set.map ctxt tgt in
                  src, tgt
              in
              s' := add !s' (ctxt g) (n-1) (src,tgt)
            ) (List.assoc_all y term_paths)
          ) (List.assoc_all x init_paths)
        with
        | Exit -> ()
      ) (generators ~n s)
    done;
    !s'
*)
  (** Graphviz representation of a set of generators and their boundary. *)
  let dot s gg =
    let n = dim s (Set.element gg) in
    assert (n > 0);
    assert (Set.for_all (fun g -> dim s g = n) gg);
    let graph = ref "" in
    let print s = graph := !graph^s in
    print "digraph {\n";
    Set.iter (fun g ->
      print ("  "^g^"[shape=box];\n");
      let src = source s g in
      let tgt = target s g in
      Set.iter (fun g' -> print (Printf.sprintf "  %s -> %s;\n" g' g)) src;
      Set.iter (fun g' -> print (Printf.sprintf "  %s -> %s;\n" g g')) tgt
    ) gg;
    print "}\n";
    !graph
end
module Sig = Signature

(** Formal cells. *)
module Cell = struct
  (** An "augmented directed complex". *)
  type t = Set.t array

  (** Raised when a cell is not a valid one. *)
  exception Invalid of string

  let make s c : t =
    let n = Array.length c in
    for i = 0 to n-1 do
      assert (Set.for_all (fun g -> Sig.mem s g && Sig.dim s g = i) c.(i))
    done;
    c

  let empty : t = [||]

  (** Cell with all the generators of a signature. *)
  let full s =
    let n = Sig.max_dim s in
    let c = Array.init (n+1) (fun n -> Sig.generators ~n s) in
    make s c

  (** Dimension. *)
  let dim (c : t) =
    let n = Array.length c - 1 in
    assert (n >= 0);
    n

  (** Generators in given dimension. *)
  let elements c n =
    c.(n)

  (** String representation of a cell. *)
  let to_string (c : t) =
    let c = Array.to_list c in
    let c = List.map (fun x -> Set.to_string x) c in
    let c = String.concat " ; " c in
    "[ " ^ c ^ " ]"

  (** Inclusion partial order. *)
  let included c d =
    assert (dim c = dim d);
    Array.for_all2 (fun x y -> Set.included x y) c d

  (** Equality of cells. *)
  let eq c d =
    assert (dim c = dim d);
    Array.for_all2 (fun x y -> Set.eq x y) c d

  let map2 s f c d =
    assert (dim c = dim d);
    make s (Array.init (dim c + 1) (fun i -> f c.(i) d.(i)))

  let union s c d = map2 s Set.union c d

  let diff s c d = map2 s Set.diff c d

  let inter s c d = map2 s Set.inter c d

  (** Closure of a cell under faces. *)
  let closure s c =
    let n = dim c in
    let c = Array.copy c in
    for i = n-1 downto 0 do
      c.(i) <- Set.union c.(i) (Set.bind (fun g -> Set.union (Sig.source s g) (Sig.target s g)) c.(i+1))
    done;
    make s c

  (** Closure of a homogeneous set of generators. *)
  let generators s n gg =
    assert (Set.for_all (fun g -> Sig.dim s g = n) gg);
    let c = Array.make (n+1) Set.empty in
    c.(n) <- gg;
    closure s c

  (** Closure of a (non-homogeneous) list of generators. *)
  let generators_list s ?n gg =
    assert (gg <> []);
    let n =
      match n with
      | None ->
         List.fold_left (fun n g -> max n (Sig.dim s g)) (-1) gg
      | Some n ->
         assert (List.for_all (fun g -> n >= Sig.dim s g) gg);
         n
    in
    let c = Array.make (n+1) Set.empty in
    List.iter (fun g ->
      let n = Sig.dim s g in
      c.(n) <- Set.add c.(n) g
    ) gg;
    closure s c

  (** Cell corresponding to a generator. *)
  let generator s g =
    generators s (Sig.dim s g) (Set.singleton g)

  (** Identity on a cell. *)
  let id s c =
    let n = dim c in
    let c = Array.init (n+2) (fun i -> if i = n+1 then Set.empty else c.(i)) in
    make s c

  (** Truncation. *)
  let trunc s c =
    let n = dim c in
    assert (n > 0);
    make s (Array.sub c 0 n)

  (** Closure of the sources of a homogeneous set of generators. *)
  let sources s n gg =
    assert (n > 0);
    assert (Set.for_all (fun g -> Sig.dim s g = n) gg);
    let gg = Set.bind (Sig.source s) gg in
    generators s (n-1) gg

  (** Closure of the targets of a homogeneous set of generators. *)
  let targets s n gg =
    assert (n > 0);
    assert (Set.for_all (fun g -> Sig.dim s g = n) gg);
    let gg = Set.bind (Sig.target s) gg in
    generators s (n-1) gg

  (** Remove generators along with their sources. This should not be used for
      non-top-dimensional cells unless you really know what you are doing. *)
  let remove_sources s c gg =
    if Set.is_empty gg then c else
      let n = dim c in
      assert (n > 0);
      let k = Sig.dim s (Set.element gg) in
      assert (Set.for_all (fun g -> Set.mem c.(k) g) gg);
      let c = diff s c (iter (n-k+1) (id s) (sources s k gg)) in
      c.(k) <- Set.minus c.(k) gg;
      closure s c

  (** Remove generators along with their targets. *)
  let remove_targets s c gg =
    if Set.is_empty gg then c else
      let n = dim c in
      assert (n > 0);
      let k = Sig.dim s (Set.element gg) in
      assert (Set.for_all (fun g -> Set.mem c.(k) g) gg);
      let c = diff s c (iter (n-k+1) (id s) (targets s k gg)) in
      c.(k) <- Set.minus c.(k) gg;
      closure s c

  (** Source of a cell. *)
  let source s c =
    let n = dim c in
    assert (n > 0);
    let c = remove_targets s c c.(n) in
    trunc s c

  (** Target of a cell. *)
  let target s c =
    let n = dim c in
    assert (n > 0);
    let c = remove_sources s c c.(n) in
    trunc s c

  (** Check that a cell is sensible. *)
  let rec check ?(downward=true) s c =
    let check = check ~downward:false in
    (* Printf.printf "check: %s\n%!" (to_string c); *)
    assert (dim c >= 0);
    if dim c = 0 then
      (if not (Set.is_singleton c.(0)) then raise (Invalid "non-singleton point"))
    else
      (
        (* Check that the cell is downward closed. *)
        if downward then
          for i = 1 to dim c do
            Set.iter (fun g ->
              if not (Set.included (Sig.source s g) c.(i-1)) then raise (Invalid "not downward closed");
              if not (Set.included (Sig.target s g) c.(i-1)) then raise (Invalid "not downward closed")
            ) c.(i)
          done;
        (* This is superfluous. *)
        (*
        if Set.is_empty c.(0) then raise Invalid;
        (* Check that cell is 0-connected. *)
        let r = Equiv.make (Set.to_list c.(0)) in
        let r = ref r in
        Set.iter (fun g ->
          let x = Set.element (Sig.source s g) in
          let y = Set.element (Sig.target s g) in
          r := Equiv.add !r x y
        ) c.(1);
        if not (Equiv.is_full !r) then raise Invalid;
        *)
        (* Check that sources (resp targets) are disjoint. *)
        Set.iter_ordered_pairs (fun g1 g2 ->
          if not (Set.is_empty (Set.inter (Sig.source s g1) (Sig.source s g2))) then raise (Invalid ("intersecting sources: "^g1^" and "^g2));
          if not (Set.is_empty (Set.inter (Sig.target s g1) (Sig.target s g2))) then raise (Invalid ("intersecting targets: "^g1^" and "^g2));
        ) c.(dim c);
        (* Check that iterated sources and targets are valid. *)
        check s (source s c);
        check s (target s c)
      )

  (*
  (** Heuristic to check the orientation of cells. *)
  let check_orientation s c =
    for i = 0 to dim c - 1 do
      let movements = c.(i+1) in
      (* Elements which are not in a target. *)
      let minimal =
        Set.filter (fun g ->
          Set.for_all (fun g' -> not (Set.mem (Sig.target s g') g)) movements
        ) c.(i)
      in
      (* Elements which are not in a source. *)
      let maximal =
        Set.filter (fun g ->
          Set.for_all (fun g' -> not (Set.mem (Sig.source s g') g)) movements
        ) c.(i)
      in
      ()
    done
  *)

  (** Check that a signature is sensible. *)
  let check_signature s =
    (* Street's acyclicity axiom 3a. *)
    (* TODO: think about implementing axiom 3b? *)
    let () =
      let last = ref "" in
      try
        for n = 1 to Sig.max_dim s do
          (* Printf.printf "n: %d\n%!" n; *)
          let gn = Set.to_list (Sig.generators ~n s) in
          let le = Poset.create gn in
          List.iter_pairs (fun g1 g2 ->
            (* Printf.printf "%d: %s vs %s\n%!" n g1 g2; *)
            last := g2;
            if not (Set.is_empty (Set.inter (Sig.target s g1) (Sig.source s g2))) then Poset.add le g1 g2
          ) gn gn
        done
      with
      | Poset.Cyclic -> raise (Sig.Invalid ("cylic: " ^ !last ^ " is possibly wrongly oriented"))
    in
    (* Source and target are cells. *)
    Set.iter (fun g ->
      if Sig.dim s g = 0 then
        (
          assert (Set.is_empty (Sig.source s g));
          assert (Set.is_empty (Sig.target s g))
        )
      else
        let g = generator s g in
        check s (source s g);
        check s (target s g)
    ) (Sig.generators s);
    (* Globular identities *)
    for n = 2 to Sig.max_dim s do
      Set.iter (fun g ->
        let g = generator s g in
        if not (eq (source s (source s g)) (source s (target s g))) then raise (Sig.Invalid "not globular");
        if not (eq (target s (source s g)) (target s (target s g))) then raise (Sig.Invalid "not globular")
      ) (Sig.generators ~n s)
    done
end

(** Cells in free omega-categories. *)
module Cat = struct
  type t =
    | Gen of generator
    | Id of t
    | Seq of int * t list (** sequential composition *)

  let rec to_string ?(pa=false) = function
    | Gen g -> g
    | Id c -> if !show_identities then "id(" ^ to_string ~pa:false c ^ ")" else to_string ~pa:true c
    | Seq (n,cc) ->
       let cc = if !composition = `Categorical then List.rev cc else cc in
       let cc = String.concat_map (" *"^(if !use_utf8 then UTF8.subscript n else string_of_int n)^" ") (to_string ~pa:true) cc in
       if pa then Printf.sprintf "(%s)" cc else cc

  let generator g = Gen g

  let simpl s c =
    let rec max_dim = function
      | Gen g -> Sig.dim s g
      | Id c -> max_dim c
      | Seq (n,cc) -> List.fold_left max (-1) (List.map max_dim cc)
    in
    let rec simpl = function
      | Seq (n, []) -> failwith "TODO: generate identities"
      | Seq (n, [c]) -> simpl c
      | Seq (n, cc) ->
         let cc = List.map simpl cc in
         let rec aux ch = function
           | c::ct when max_dim c <= n -> aux ch ct
           | (Seq(n',cc))::ct when n' = n -> aux ch (cc@ct)
           | c::ct -> aux (c::ch) ct
           | [] -> Seq (n, List.rev ch)
         in
         aux [] cc
      (* | Id c -> Id (simpl c) *)
      | Id c ->
         (
           match simpl c with
           | Seq (n, cc) ->
              let cc = List.map (fun c -> Id c) cc in
              let c = Seq (n, cc) in
              simpl c
           | c -> Id c
         )
      | Gen _ as c -> c
    in
    simpl c

  (** Categorical decomposition of a cell. *)
  let rec of_cell (* ?(depth=0) *) s c =
    (* let of_cell ?(depth=depth+1) s c = of_cell ~depth s c in *)
    (* Printf.printf "%sof_cell: %s\n%!" (String.make (2*depth) ' ') (Cell.to_string c); *)
    Cell.check s c;
    let n = Cell.dim c in
    let b = c.(n) in
    if n = 0 then
      (
        if not (Set.is_singleton b) then raise (Cell.Invalid "non-singleton point");
        Gen (Set.element b)
      )
    else if Set.is_empty b then
      Id (of_cell s (Array.sub c 0 n))
    (* Only one top-dimensional cell. *)
    else if Set.is_singleton b then
      let g = Set.element b in
      (* Find the maximal dimension below n where there are cells other than
         faces of g. *)
      let c' = Cell.diff s c (Cell.generator s g) in
      let rec aux k =
        if k = (-1) then -1
        else if not (Set.is_empty c'.(k)) then k
        else aux (k-1)
      in
      let k = aux (n-1) in
      if k = 0 then
        (* The cell is not connected. *)
        raise (Cell.Invalid "disconnected");
      if k = -1 then Gen g else
        let b = c.(k) in
        let le = Sig.le s b in
        let le = Poset.le le in
        let cg = Cell.generator s g in
        (* Cells before g. *)
        let bs =
          Set.filter (fun g ->
            not (Set.mem cg.(k) g)
            && Set.exists (fun h -> le g h) cg.(k)
          ) b
        in
        (* Cells after (or in parallel with) g. *)
        let bt =
          Set.filter (fun g ->
            not (Set.mem cg.(k) g)
            && Set.for_all (fun h -> not (le g h)) cg.(k)
          ) b
        in
        (* Printf.printf "k: %d\n%!" k; *)
        (* Printf.printf "before: %s\n%!" (Set.to_string bs); *)
        (* Printf.printf "after : %s\n%!" (Set.to_string bt); *)
        assert (Set.is_empty (Set.inter bs bt));
        let cs = Cell.remove_targets s c bt in
        let cs = Cell.diff s cs (Cell.diff s cg (iter (n-k+1) (Cell.id s) (iter (n-k+1) (Cell.source s) cg))) in
        let cs = Cell.closure s cs in
        let cg = Cell.remove_sources s (Cell.remove_targets s c bt) bs in
        (* let ct = Cell.remove_sources s (Cell.remove_sources s c bs) (Set.singleton g) in *)
        let ct = Cell.remove_sources s c bs in
        let ct = Cell.diff s ct (Cell.diff s cg (iter (n-k+1) (Cell.id s) (iter (n-k+1) (Cell.target s) cg))) in
        let ct = Cell.closure s ct in
        (* Printf.printf "cell before: %s\n%!" (Cell.to_string cs); *)
        (* Printf.printf "cell middle: %s\n%!" (Cell.to_string cg); *)
        (* Printf.printf "cell after : %s\n%!" (Cell.to_string ct); *)
        let cs = of_cell s cs in
        let cg = of_cell s cg in
        let ct = of_cell s ct in
        Seq (k-1, [cs;cg;ct])
    (* Multiple top-dimensional cells. *)
    else
      (* For now we only consider compositions in dimension n-1, but we could do
         better by trying to compose in the lowest dimension. *)
      let le = Sig.le s b in
      let b = Set.to_list b in
      let b = Poset.sort_list le b in
      let b =
        List.map_ctx (fun bh g bt ->
          let c = Cell.remove_sources s c (Set.make bh) in
          let c = Cell.remove_targets s c (Set.make bt) in
          c
        ) b
      in
      let b = List.map (of_cell s) b in
      Seq (n-1,b)

  (** String representation of a signature with categorical sources and targets. *)
  let string_of_sig s =
    let ans = ref "" in
    let sc n c =
      let c = Cell.generators s n c in
      let c = of_cell s c in
      let c = simpl s c in
      to_string c
    in
    Set.iter (fun g -> ans := !ans ^ g ^ "\n") (Sig.generators ~n:0 s);
    for n = 1 to Sig.max_dim s do
      ans := !ans ^ "\n";
      Set.iter (fun g ->
        ans := !ans ^ Printf.sprintf "%s : %s -> %s\n%!" g
          (sc (n-1) (Sig.source s g))
          (sc (n-1) (Sig.target s g))
      ) (Sig.generators ~n s);
    done;
    !ans
end
