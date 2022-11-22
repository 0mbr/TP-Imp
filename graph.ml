type tag = Conflict | Preference
module RMap = Map.Make(Aimp.Register)
module VMap = Map.Make(String)
type graph = tag RMap.t RMap.t

(* Graphe :

"r1" ----I---- "r2"
"r1" ----P---- "r3"

r1 |--> ( r2 |--> I,  r3 |--> P )
r2 |--> ( r1 |--> I )
r3 |--> ( r1 |--> P )

*)

let rs = Aimp.rname

let empty = RMap.empty
let add_vertex x g =
  if RMap.mem x g then g
  else RMap.add x RMap.empty g

let update_edge x y t g =
  assert (RMap.mem x g);
  let v = RMap.find x g in
  match RMap.find_opt y v, t with
  | None, _ | Some Preference, Conflict ->
     RMap.add x (RMap.add y t v) g
  | _ -> g

let add_edge x y t g =
  assert (x <> y);
  let g = add_vertex x (add_vertex y g) in
  update_edge x y t (update_edge y x t g)

let remove_vertex x g =
  RMap.map (RMap.remove x) (RMap.remove x g)

module RSet = Set.Make(Aimp.Register)
module VSet = Set.Make(String)

let neighbours x t g =
  if not (RMap.mem x g) then
    (Printf.printf "Vertex %s not found (function neighbours).\n" (rs x);
     assert false)
  else
    RMap.fold 
      (fun y u v -> if t = u then RSet.add y v else v)
      (RMap.find x g)
      RSet.empty

let degree x g =
  RSet.cardinal (neighbours x Conflict g)

let conflict x y g =
  match RMap.find_opt x g with
  | None -> false
  | Some v -> RMap.find_opt y v = Some Conflict

let has_pref x g =
  RMap.exists (fun _ t -> t = Preference) (RMap.find x g)

let remove_prefs x g =
  RMap.add x (RMap.filter (fun _ t -> t <> Preference) (RMap.find x g)) g

let merge_vertices x y v =
  let v' = RMap.remove x v in
  match RMap.find_opt x v, RMap.find_opt y v with
  | None, None -> v'
  | Some Conflict, _ | _, Some Conflict -> RMap.add y Conflict v'
  | _ -> RMap.add y Preference v'

let merge_neighbours =
  RMap.union (fun k t1 t2 -> 
      match t1, t2 with
      | Conflict, _ | _, Conflict -> Some Conflict
      | Preference, Preference    -> Some Preference) 

let merge x y g =
  Printf.printf "Merge %s into %s.\n" (rs x) (rs y);
  RMap.filter_map (fun z v ->
      if z = x then
        None
      else if z = y then
        Some (RMap.remove x (RMap.remove y (merge_neighbours (RMap.find x g) v)))
      else
        Some (merge_vertices x y v)
    ) g

let rset_to_vset regset =
  (RSet.fold (fun r s -> VSet.add (rs r) s) (regset) VSet.empty)

let print_graph g =
  Printf.(
    printf "Graphe d'interférence :\n";
    RMap.iter (fun x _ ->
        printf "  %s:" (rs x);
        VSet.iter (printf " %s") (rset_to_vset (neighbours x Conflict g));
        printf "\n    | ";
        VSet.iter (printf " %s") (rset_to_vset (neighbours x Preference g));
        printf "\n")
      g
  )

