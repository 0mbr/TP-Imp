let index l e =
  let rec cp l i = match l with
    | [] -> failwith (Printf.sprintf "%s n'as pas été trouvé dans la liste spécifiée" e)
    | h::t when h = e -> i
    | _::t -> cp t (i+1)
  in
  cp l 0