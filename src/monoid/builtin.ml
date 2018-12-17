(** Functions which are registered by default. Most functions should register
    themselves locally. *)

(* TODO: put save, undo, etc. in lang directly *)

open Standard
open Timeout
open LangMonoid

module M = FreeMonoid

let () =
  let printf = Lang.printf in
  let handlers =
    [      
      
      "rgkb", 
      ("Try words of given length for completion (only 2 for now).", 1, fun rs a ->
        (* We only try length 2 and 3 for now. *)
        if int_of_string a.(0) = 3 then
          for i = 0 to M.nb_generators rs - 1 do
            for j = 0 to M.nb_generators rs - 1 do
              for k = 0 to M.nb_generators rs - 1 do
                let w = rs.M.generators.(i) ^ rs.M.generators.(j) ^ rs.M.generators.(k) in
                try
                  printf "Trying generator: %s.\n%!" w;
                  let rs = rgen rs w in
                  let rs = Timeout.timeout !Lang.timeout (M.canonized_completion ~lt) rs in
                  printf "%s\n%!" (M.to_string rs)
                with
                | Timeout -> ()
              done
            done
          done
        else
          for i = 0 to M.nb_generators rs - 1 do
            for j = 0 to M.nb_generators rs - 1 do
              let w = rs.M.generators.(i) ^ rs.M.generators.(j) in
              try
                printf "Trying generator: %s.\n%!" w;
                let rs = rgen rs w in
                let rs = Timeout.timeout !Lang.timeout (M.canonized_completion ~lt) rs in
                printf "%s\n%!" (M.to_string rs)
              with
              | Timeout -> ()
            done
          done;
        rs
      );
      
      "orient", 
      ("Orient rules in order to respect current order.", 0, fun rs a -> M.orient rs (lt rs));
      
      "canonize", 
      ("Canonize the rewriting system (remove left-inclusions and normalize right members).", 0, fun rs a -> 
        M.canonize ~lt rs
      );
      
      "normalize", 
      ("Normalize a word.", 1, fun rs a ->
        let r = M.normalize_path rs (w a.(0)) in
        printf "%s\n%!" (if r = [] then sw (M.CRules.target rs r) else sr rs r);
        rs
      );
      
      "cp", 
      ("Critical pairs.", 0, fun rs a ->
        let cp = M.critical_pairs rs in
        List.iter (fun (l,r) -> printf "%s\n%s\n\n%!" (sr rs [l]) (sr rs [r])) cp;
        rs
      );
      
      "ccp", 
      ("Cocritical pairs.", 0, fun rs a ->
        let cp = M.cocritical_pairs rs in
        List.iter (fun (l,r) -> printf "%s\n%s\n\n%!" (sr rs [l]) (sr rs [r])) cp;
        rs
      );
      
      "leq", 
      ("Check whether a word is smaller than another one with the current completion order.", 2, fun rs a ->
        let w0 = w a.(0) in
        let w1 = w a.(1) in
        printf "%B\n%!" (lt rs w0 w1);
        rs
      );
      
      "ncp", 
      ("Normalized critical pairs.", 0, fun rs a ->
        let eqs = M.critical_rules lt rs in
        let rec aux n = function
	  | [] -> ()
	  | (l, r) :: eqs -> 
	     printf "%i : %s <-> %s\n%!" n (sw l) (sw r) ;
	    aux (n-1) eqs
        in 
        let n = List.length eqs in
        aux n (List.rev eqs) ; 
        printf "We have %i nonconfluent critical branchings.\n%!" n ;
        let rs = 
	  if n > 0 then (
	    printf "How many equations shall we add?\n%!";
	    try 
	      let k = read_int () in
	      printf "Adding the first %i equations.\n%!" k;
	      let eqs = List.first_n_elts k eqs in
	      let rs = M.add_rules rs eqs in
	      M.canonize lt rs
	    with 
	    | _ -> rs
	  ) 
	  else rs
        in rs
      );
      
      "add", 
      ("Add n rules corresponding to the first n nonconfluent critical pairs.", 1, fun rs a -> 
        M.addncp ~lt rs (int_of_string a.(0))
      );

      (*
      "nccp", 
      ("Normalized cocritical pairs.", 0, fun rs a ->
        List.iter
	  (fun (l,r) ->
	    let l,r = if lt rs r l then (l,r) else (r,l) in
	    if l <> r then printf "%s <-> %s\n%!" (sw l) (sw r)
	  ) (M.cocritical_rules rs);
        rs
      );
       *)

      "nccp",
      ("Non-confluent critical pairs.", 0, fun rs a ->
        let cp = M.critical_pairs rs in
        List.iter (fun (l,r) ->
          let l' = M.normalize_path rs (M.CRule.target rs l) in
          let r' = M.normalize_path rs (M.CRule.target rs r) in
          let l = M.CRules.cons l l' in
          let r = M.CRules.cons r r' in
          if not (M.W.eq (M.CRules.target rs l) (M.CRules.target rs r)) then
            Lang.printf "%s\n%s\n\n" (M.CRules.to_string rs l) (M.CRules.to_string rs r)
          ) cp;
        rs
      );
      
      "incp", 
      ("Interactive completion by orienting critical rules.", 0, fun rs a ->
        let cr = M.critical_rules lt rs in
        let cr = List.filter (fun (l,r) -> l <> r) cr in
        let cr = List.map (fun (l,r) -> if lt rs r l then l,r else r,l) cr in
        let cr = Array.of_list cr in
        Array.iteri (fun i (l,r) -> printf "%d : %s <-> %s\n%!" i (sw l) (sw r)) cr;
        printf "Which rule do we orient?\n";
        let n = read_int () in
        let l,r = cr.(n) in
        printf "How do we orient %s <-> %s?\n(1) to left (2) to right\n%!" (sw l) (sw r);
        let c = ref ' ' in
        while !c <> '1' && !c <> '2' do
          flush stdout;
          c := input_char stdin
        done;
        printf "You chose %c.\n%!" !c;
        let rs =
          if !c = '1' then
            add_rule rs (r,l)
          else if !c = '2' then
            add_rule rs (l,r)
          else assert false
        in
        rs
      );
      
      "cu", 
      ("Critucal uples.", 1, fun rs a ->
        let cu = M.critical_uples rs (int_of_string a.(0)) in
        List.iter (fun cu -> List.iter (fun r -> printf "%s\n" (sr rs [r])) cu; printf "\n%!") cu;
        printf "We have %d %s-uples.\n" (List.length cu) a.(0);
        rs
      );
      
      "kb", 
      ("Knuth-Bendix completion.", 0, fun rs a -> M.completion ~lt rs);
      
      "kbc", 
      ("Canonized Knuth-Bendix completion.", 0, fun rs a -> M.canonized_completion ~lt rs);
      
      "kbone", 
      ("Canonized Knuth-Bendix one-relation completion.", 0, fun rs a -> M.completion_one ~lt rs);
      
      "kbs", 
      ("One step of Knuth-Bendix completion.", 0, fun rs a -> M.completion_step ~lt rs);
      
      "kbsc", 
      ("One step of canonized Knuth-Bendix completion.", 0, fun rs a -> 
        M.canonize ~lt (M.completion_step ~lt rs)
      );
      
      "ikb", 
      ("Interactive Knuth-Bendix completion.", 0, fun rs a ->
        let ord = ref [] in
        let global_lt = lt in
        let rec lt rs u v =
          try
            List.assoc (u,v) !ord
          with
          | Not_found ->
	     let u,v = if global_lt rs v u then u,v else v,u in
             printf "How shall we solve %s <-> %s?\n(1) orient to the left (2) orient to the right (3) add a generator \n%!" (sw u) (sw v);
             let c = ref ' ' in
             while !c <> '1' && !c <> '2' && !c <> '3' do
               flush stdout;
               c := input_char stdin
             done;
             printf "You chose %c.\n%!" !c;
             if !c = '1' then
               ord := ((u,v),true)::((v,u),false) :: !ord
             else if !c = '2' then
               ord := ((u,v),false)::((v,u),true) :: !ord
             else if !c = '3' then
               ord := ((u,v),true)::((v,u),true) :: !ord
	     else assert false;
             lt rs u v
        in
        (M.canonize global_lt (M.completion_step ~lt rs))
      );
      
      "hbasis", 
      ("Display a homotopy basis of the rewriting system.", 0, fun rs a ->
        let hbasis = M.hbasis rs in
        List.iter (fun (r1,r2) -> printf "%s\n%s\n\n%!" (sr rs r1) (sr rs r2)) hbasis;
        printf "We have %d homotopy generators.\n%!" (List.length hbasis);
        rs
      );

      "shbasis",
      ("Save a homotopy basis of the rewriting system.", 1, fun rs a ->
        let oc = open_out a.(0) in 
        let hbasis = M.hbasis rs in
        List.iter 
	  (fun (r1,r2) -> 
	    let str = Printf.sprintf "%s\n%s\n\n%!" (sr rs r1) (sr rs r2)
	    in output_string oc str
	  ) 
	  hbasis ; 
        let str = Printf.sprintf "We have %d homotopy generators.\n%!" (List.length hbasis)
        in output_string oc str;
        close_out oc ;
        rs
      );
      
      "rhbasis", 
      ("Display a reduced homotopy basis of the rewriting system.", 0, fun rs a ->
        let hbasis = M.reduced_hbasis rs in
        List.iter (fun (r1,r2) -> printf "%s\n%s\n\n%!" (sr rs r1) (sr rs r2)) hbasis;
        printf "We have %d homotopy generators.\n%!" (List.length hbasis);
        rs
      );

      "srhbasis",
      ("Save a reduced homotopy basis of the rewriting system.", 1, fun rs a ->
        let oc = open_out a.(0) in 
        let hbasis = M.reduced_hbasis rs in
        List.iter 
	  (fun (r1,r2) -> 
	    let str = Printf.sprintf "%s\n%s\n\n%!" (sr rs r1) (sr rs r2)
	    in output_string oc str
	  ) 
	  hbasis ; 
        let str = Printf.sprintf "We have %d homotopy generators.\n%!" (List.length hbasis)
        in output_string oc str;
        close_out oc ;
        rs
      );
      
      "save", 
      ("Save current rewriting system in a file.", 1, fun rs a ->
        let oc = open_out a.(0) in
        output_string oc ("order " ^ !LangMonoid.order ^ "\n");
        for i = 0 to Array.length rs.M.generators - 1 do
          output_string oc ("gen " ^ rs.M.generators.(i) ^ "\n")
        done;
        M.IMap.iter (fun _ (r1,r2) -> output_string oc ("rule " ^ sw r1 ^ " " ^ sw r2 ^ "\n")) rs.M.rules;
        close_out oc;
        rs);

    ]
  in
  List.iter (fun (name, (doc, args, f)) -> LangMonoid.register name doc args f) handlers
